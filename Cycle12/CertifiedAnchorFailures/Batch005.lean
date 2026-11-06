import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch010
import Cycle12.CountingCertificates.Batch011
import Cycle12.CutFailureCertificates.Budget010
import Cycle12.CutFailureCertificates.Budget011
import Cycle12.MergedCutGroups.Batch025
import Cycle12.MergedCutGroups.Batch026
import Cycle12.MergedCutGroups.Batch027
import Cycle12.MergedCutGroups.Batch028
import Cycle12.MergedCutGroups.Batch029
import Cycle12.PopulationCertificates.Batch010
import Cycle12.PopulationCertificates.Batch011
import Cycle12.WitnessCertificates.Batch010
import Cycle12.WitnessCertificates.Batch011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch005
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches100 : (MergedCutGroups.Batch025.certificate302).AnchorMatches CountingCertificates.Batch010.certificate201 := by decide +kernel
theorem exponentialBound100 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate302).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate201).dm (WitnessCertificates.Batch010.certificate201).beta (WitnessCertificates.Batch010.certificate201).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate201).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch025.certificate302).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate201).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch025.certificate302 CountingCertificates.Batch010.certificate201 matches100 MergedCutGroups.Batch025.numericValid302 MergedCutGroups.Batch025.cellsSound302 MergedCutGroups.Batch025.cellsNumeric302 MergedCutGroups.Batch025.populationMatches302
    PopulationCertificates.Batch010.valid201 PopulationCertificates.Batch010.sound201 WitnessCertificates.Batch010.valid201 WitnessCertificates.Batch010.sound201 CountingCertificates.Batch010.valid201 CountingCertificates.Batch010.sound201 H st hI
theorem probabilityBound100 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate302).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate201).dm (WitnessCertificates.Batch010.certificate201).beta (WitnessCertificates.Batch010.certificate201).L) ≤ ((CutFailureCertificates.Budget010.certificate201).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound201 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate201).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate302).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate201).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate201).bound:ℝ) at hb
  exact (exponentialBound100 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches101 : (MergedCutGroups.Batch025.certificate305).AnchorMatches CountingCertificates.Batch010.certificate203 := by decide +kernel
theorem exponentialBound101 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate305).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate203).dm (WitnessCertificates.Batch010.certificate203).beta (WitnessCertificates.Batch010.certificate203).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate203).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch025.certificate305).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate203).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch025.certificate305 CountingCertificates.Batch010.certificate203 matches101 MergedCutGroups.Batch025.numericValid305 MergedCutGroups.Batch025.cellsSound305 MergedCutGroups.Batch025.cellsNumeric305 MergedCutGroups.Batch025.populationMatches305
    PopulationCertificates.Batch010.valid203 PopulationCertificates.Batch010.sound203 WitnessCertificates.Batch010.valid203 WitnessCertificates.Batch010.sound203 CountingCertificates.Batch010.valid203 CountingCertificates.Batch010.sound203 H st hI
theorem probabilityBound101 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate305).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate203).dm (WitnessCertificates.Batch010.certificate203).beta (WitnessCertificates.Batch010.certificate203).L) ≤ ((CutFailureCertificates.Budget010.certificate203).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound203 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate203).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate305).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate203).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate203).bound:ℝ) at hb
  exact (exponentialBound101 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches102 : (MergedCutGroups.Batch025.certificate308).AnchorMatches CountingCertificates.Batch010.certificate205 := by decide +kernel
theorem exponentialBound102 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate308).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate205).dm (WitnessCertificates.Batch010.certificate205).beta (WitnessCertificates.Batch010.certificate205).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate205).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch025.certificate308).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate205).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch025.certificate308 CountingCertificates.Batch010.certificate205 matches102 MergedCutGroups.Batch025.numericValid308 MergedCutGroups.Batch025.cellsSound308 MergedCutGroups.Batch025.cellsNumeric308 MergedCutGroups.Batch025.populationMatches308
    PopulationCertificates.Batch010.valid205 PopulationCertificates.Batch010.sound205 WitnessCertificates.Batch010.valid205 WitnessCertificates.Batch010.sound205 CountingCertificates.Batch010.valid205 CountingCertificates.Batch010.sound205 H st hI
theorem probabilityBound102 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate308).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate205).dm (WitnessCertificates.Batch010.certificate205).beta (WitnessCertificates.Batch010.certificate205).L) ≤ ((CutFailureCertificates.Budget010.certificate205).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound205 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate205).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate308).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate205).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate205).bound:ℝ) at hb
  exact (exponentialBound102 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches103 : (MergedCutGroups.Batch025.certificate311).AnchorMatches CountingCertificates.Batch010.certificate207 := by decide +kernel
theorem exponentialBound103 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate311).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate207).dm (WitnessCertificates.Batch010.certificate207).beta (WitnessCertificates.Batch010.certificate207).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate207).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch025.certificate311).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate207).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch025.certificate311 CountingCertificates.Batch010.certificate207 matches103 MergedCutGroups.Batch025.numericValid311 MergedCutGroups.Batch025.cellsSound311 MergedCutGroups.Batch025.cellsNumeric311 MergedCutGroups.Batch025.populationMatches311
    PopulationCertificates.Batch010.valid207 PopulationCertificates.Batch010.sound207 WitnessCertificates.Batch010.valid207 WitnessCertificates.Batch010.sound207 CountingCertificates.Batch010.valid207 CountingCertificates.Batch010.sound207 H st hI
theorem probabilityBound103 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate311).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate207).dm (WitnessCertificates.Batch010.certificate207).beta (WitnessCertificates.Batch010.certificate207).L) ≤ ((CutFailureCertificates.Budget010.certificate207).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound207 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate207).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate311).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate207).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate207).bound:ℝ) at hb
  exact (exponentialBound103 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches104 : (MergedCutGroups.Batch026.certificate314).AnchorMatches CountingCertificates.Batch010.certificate209 := by decide +kernel
theorem exponentialBound104 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate314).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate209).dm (WitnessCertificates.Batch010.certificate209).beta (WitnessCertificates.Batch010.certificate209).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate209).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch026.certificate314).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate209).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch026.certificate314 CountingCertificates.Batch010.certificate209 matches104 MergedCutGroups.Batch026.numericValid314 MergedCutGroups.Batch026.cellsSound314 MergedCutGroups.Batch026.cellsNumeric314 MergedCutGroups.Batch026.populationMatches314
    PopulationCertificates.Batch010.valid209 PopulationCertificates.Batch010.sound209 WitnessCertificates.Batch010.valid209 WitnessCertificates.Batch010.sound209 CountingCertificates.Batch010.valid209 CountingCertificates.Batch010.sound209 H st hI
theorem probabilityBound104 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate314).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate209).dm (WitnessCertificates.Batch010.certificate209).beta (WitnessCertificates.Batch010.certificate209).L) ≤ ((CutFailureCertificates.Budget010.certificate209).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound209 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate209).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate314).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate209).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate209).bound:ℝ) at hb
  exact (exponentialBound104 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches105 : (MergedCutGroups.Batch026.certificate317).AnchorMatches CountingCertificates.Batch010.certificate211 := by decide +kernel
theorem exponentialBound105 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate317).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate211).dm (WitnessCertificates.Batch010.certificate211).beta (WitnessCertificates.Batch010.certificate211).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate211).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch026.certificate317).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate211).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch026.certificate317 CountingCertificates.Batch010.certificate211 matches105 MergedCutGroups.Batch026.numericValid317 MergedCutGroups.Batch026.cellsSound317 MergedCutGroups.Batch026.cellsNumeric317 MergedCutGroups.Batch026.populationMatches317
    PopulationCertificates.Batch010.valid211 PopulationCertificates.Batch010.sound211 WitnessCertificates.Batch010.valid211 WitnessCertificates.Batch010.sound211 CountingCertificates.Batch010.valid211 CountingCertificates.Batch010.sound211 H st hI
theorem probabilityBound105 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate317).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate211).dm (WitnessCertificates.Batch010.certificate211).beta (WitnessCertificates.Batch010.certificate211).L) ≤ ((CutFailureCertificates.Budget010.certificate211).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound211 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate211).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate317).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate211).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate211).bound:ℝ) at hb
  exact (exponentialBound105 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches106 : (MergedCutGroups.Batch026.certificate320).AnchorMatches CountingCertificates.Batch010.certificate213 := by decide +kernel
theorem exponentialBound106 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate320).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate213).dm (WitnessCertificates.Batch010.certificate213).beta (WitnessCertificates.Batch010.certificate213).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate213).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch026.certificate320).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate213).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch026.certificate320 CountingCertificates.Batch010.certificate213 matches106 MergedCutGroups.Batch026.numericValid320 MergedCutGroups.Batch026.cellsSound320 MergedCutGroups.Batch026.cellsNumeric320 MergedCutGroups.Batch026.populationMatches320
    PopulationCertificates.Batch010.valid213 PopulationCertificates.Batch010.sound213 WitnessCertificates.Batch010.valid213 WitnessCertificates.Batch010.sound213 CountingCertificates.Batch010.valid213 CountingCertificates.Batch010.sound213 H st hI
theorem probabilityBound106 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate320).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate213).dm (WitnessCertificates.Batch010.certificate213).beta (WitnessCertificates.Batch010.certificate213).L) ≤ ((CutFailureCertificates.Budget010.certificate213).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound213 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate213).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate320).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate213).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate213).bound:ℝ) at hb
  exact (exponentialBound106 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches107 : (MergedCutGroups.Batch026.certificate323).AnchorMatches CountingCertificates.Batch010.certificate215 := by decide +kernel
theorem exponentialBound107 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate323).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate215).dm (WitnessCertificates.Batch010.certificate215).beta (WitnessCertificates.Batch010.certificate215).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate215).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch026.certificate323).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate215).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch026.certificate323 CountingCertificates.Batch010.certificate215 matches107 MergedCutGroups.Batch026.numericValid323 MergedCutGroups.Batch026.cellsSound323 MergedCutGroups.Batch026.cellsNumeric323 MergedCutGroups.Batch026.populationMatches323
    PopulationCertificates.Batch010.valid215 PopulationCertificates.Batch010.sound215 WitnessCertificates.Batch010.valid215 WitnessCertificates.Batch010.sound215 CountingCertificates.Batch010.valid215 CountingCertificates.Batch010.sound215 H st hI
theorem probabilityBound107 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate323).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate215).dm (WitnessCertificates.Batch010.certificate215).beta (WitnessCertificates.Batch010.certificate215).L) ≤ ((CutFailureCertificates.Budget010.certificate215).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound215 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate215).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate323).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate215).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate215).bound:ℝ) at hb
  exact (exponentialBound107 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches108 : (MergedCutGroups.Batch027.certificate326).AnchorMatches CountingCertificates.Batch010.certificate217 := by decide +kernel
theorem exponentialBound108 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate326).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate217).dm (WitnessCertificates.Batch010.certificate217).beta (WitnessCertificates.Batch010.certificate217).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate217).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch027.certificate326).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate217).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch027.certificate326 CountingCertificates.Batch010.certificate217 matches108 MergedCutGroups.Batch027.numericValid326 MergedCutGroups.Batch027.cellsSound326 MergedCutGroups.Batch027.cellsNumeric326 MergedCutGroups.Batch027.populationMatches326
    PopulationCertificates.Batch010.valid217 PopulationCertificates.Batch010.sound217 WitnessCertificates.Batch010.valid217 WitnessCertificates.Batch010.sound217 CountingCertificates.Batch010.valid217 CountingCertificates.Batch010.sound217 H st hI
theorem probabilityBound108 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate326).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate217).dm (WitnessCertificates.Batch010.certificate217).beta (WitnessCertificates.Batch010.certificate217).L) ≤ ((CutFailureCertificates.Budget010.certificate217).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound217 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate217).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate326).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate217).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate217).bound:ℝ) at hb
  exact (exponentialBound108 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches109 : (MergedCutGroups.Batch027.certificate329).AnchorMatches CountingCertificates.Batch010.certificate219 := by decide +kernel
theorem exponentialBound109 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate329).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate219).dm (WitnessCertificates.Batch010.certificate219).beta (WitnessCertificates.Batch010.certificate219).L) ≤ (2*exp (-((CountingCertificates.Batch010.certificate219).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch027.certificate329).exponent:ℝ)*st.R))/((WitnessCertificates.Batch010.certificate219).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch027.certificate329 CountingCertificates.Batch010.certificate219 matches109 MergedCutGroups.Batch027.numericValid329 MergedCutGroups.Batch027.cellsSound329 MergedCutGroups.Batch027.cellsNumeric329 MergedCutGroups.Batch027.populationMatches329
    PopulationCertificates.Batch010.valid219 PopulationCertificates.Batch010.sound219 WitnessCertificates.Batch010.valid219 WitnessCertificates.Batch010.sound219 CountingCertificates.Batch010.valid219 CountingCertificates.Batch010.sound219 H st hI
theorem probabilityBound109 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate329).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch010.certificate219).dm (WitnessCertificates.Batch010.certificate219).beta (WitnessCertificates.Batch010.certificate219).L) ≤ ((CutFailureCertificates.Budget010.certificate219).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound219 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate219).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate329).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch010.certificate219).omega:ℝ)) ≤ ((CutFailureCertificates.Budget010.certificate219).bound:ℝ) at hb
  exact (exponentialBound109 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches110 : (MergedCutGroups.Batch027.certificate332).AnchorMatches CountingCertificates.Batch011.certificate221 := by decide +kernel
theorem exponentialBound110 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate332).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate221).dm (WitnessCertificates.Batch011.certificate221).beta (WitnessCertificates.Batch011.certificate221).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate221).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch027.certificate332).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate221).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch027.certificate332 CountingCertificates.Batch011.certificate221 matches110 MergedCutGroups.Batch027.numericValid332 MergedCutGroups.Batch027.cellsSound332 MergedCutGroups.Batch027.cellsNumeric332 MergedCutGroups.Batch027.populationMatches332
    PopulationCertificates.Batch011.valid221 PopulationCertificates.Batch011.sound221 WitnessCertificates.Batch011.valid221 WitnessCertificates.Batch011.sound221 CountingCertificates.Batch011.valid221 CountingCertificates.Batch011.sound221 H st hI
theorem probabilityBound110 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate332).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate221).dm (WitnessCertificates.Batch011.certificate221).beta (WitnessCertificates.Batch011.certificate221).L) ≤ ((CutFailureCertificates.Budget011.certificate221).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound221 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate221).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate332).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate221).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate221).bound:ℝ) at hb
  exact (exponentialBound110 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches111 : (MergedCutGroups.Batch027.certificate335).AnchorMatches CountingCertificates.Batch011.certificate223 := by decide +kernel
theorem exponentialBound111 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate335).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate223).dm (WitnessCertificates.Batch011.certificate223).beta (WitnessCertificates.Batch011.certificate223).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate223).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch027.certificate335).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate223).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch027.certificate335 CountingCertificates.Batch011.certificate223 matches111 MergedCutGroups.Batch027.numericValid335 MergedCutGroups.Batch027.cellsSound335 MergedCutGroups.Batch027.cellsNumeric335 MergedCutGroups.Batch027.populationMatches335
    PopulationCertificates.Batch011.valid223 PopulationCertificates.Batch011.sound223 WitnessCertificates.Batch011.valid223 WitnessCertificates.Batch011.sound223 CountingCertificates.Batch011.valid223 CountingCertificates.Batch011.sound223 H st hI
theorem probabilityBound111 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate335).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate223).dm (WitnessCertificates.Batch011.certificate223).beta (WitnessCertificates.Batch011.certificate223).L) ≤ ((CutFailureCertificates.Budget011.certificate223).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound223 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate223).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate335).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate223).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate223).bound:ℝ) at hb
  exact (exponentialBound111 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches112 : (MergedCutGroups.Batch028.certificate338).AnchorMatches CountingCertificates.Batch011.certificate225 := by decide +kernel
theorem exponentialBound112 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate338).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate225).dm (WitnessCertificates.Batch011.certificate225).beta (WitnessCertificates.Batch011.certificate225).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate225).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch028.certificate338).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate225).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch028.certificate338 CountingCertificates.Batch011.certificate225 matches112 MergedCutGroups.Batch028.numericValid338 MergedCutGroups.Batch028.cellsSound338 MergedCutGroups.Batch028.cellsNumeric338 MergedCutGroups.Batch028.populationMatches338
    PopulationCertificates.Batch011.valid225 PopulationCertificates.Batch011.sound225 WitnessCertificates.Batch011.valid225 WitnessCertificates.Batch011.sound225 CountingCertificates.Batch011.valid225 CountingCertificates.Batch011.sound225 H st hI
theorem probabilityBound112 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate338).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate225).dm (WitnessCertificates.Batch011.certificate225).beta (WitnessCertificates.Batch011.certificate225).L) ≤ ((CutFailureCertificates.Budget011.certificate225).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound225 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate225).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate338).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate225).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate225).bound:ℝ) at hb
  exact (exponentialBound112 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches113 : (MergedCutGroups.Batch028.certificate341).AnchorMatches CountingCertificates.Batch011.certificate227 := by decide +kernel
theorem exponentialBound113 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate341).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate227).dm (WitnessCertificates.Batch011.certificate227).beta (WitnessCertificates.Batch011.certificate227).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate227).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch028.certificate341).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate227).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch028.certificate341 CountingCertificates.Batch011.certificate227 matches113 MergedCutGroups.Batch028.numericValid341 MergedCutGroups.Batch028.cellsSound341 MergedCutGroups.Batch028.cellsNumeric341 MergedCutGroups.Batch028.populationMatches341
    PopulationCertificates.Batch011.valid227 PopulationCertificates.Batch011.sound227 WitnessCertificates.Batch011.valid227 WitnessCertificates.Batch011.sound227 CountingCertificates.Batch011.valid227 CountingCertificates.Batch011.sound227 H st hI
theorem probabilityBound113 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate341).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate227).dm (WitnessCertificates.Batch011.certificate227).beta (WitnessCertificates.Batch011.certificate227).L) ≤ ((CutFailureCertificates.Budget011.certificate227).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound227 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate227).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate341).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate227).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate227).bound:ℝ) at hb
  exact (exponentialBound113 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches114 : (MergedCutGroups.Batch028.certificate344).AnchorMatches CountingCertificates.Batch011.certificate229 := by decide +kernel
theorem exponentialBound114 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate344).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate229).dm (WitnessCertificates.Batch011.certificate229).beta (WitnessCertificates.Batch011.certificate229).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate229).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch028.certificate344).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate229).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch028.certificate344 CountingCertificates.Batch011.certificate229 matches114 MergedCutGroups.Batch028.numericValid344 MergedCutGroups.Batch028.cellsSound344 MergedCutGroups.Batch028.cellsNumeric344 MergedCutGroups.Batch028.populationMatches344
    PopulationCertificates.Batch011.valid229 PopulationCertificates.Batch011.sound229 WitnessCertificates.Batch011.valid229 WitnessCertificates.Batch011.sound229 CountingCertificates.Batch011.valid229 CountingCertificates.Batch011.sound229 H st hI
theorem probabilityBound114 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate344).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate229).dm (WitnessCertificates.Batch011.certificate229).beta (WitnessCertificates.Batch011.certificate229).L) ≤ ((CutFailureCertificates.Budget011.certificate229).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound229 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate229).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate344).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate229).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate229).bound:ℝ) at hb
  exact (exponentialBound114 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches115 : (MergedCutGroups.Batch028.certificate347).AnchorMatches CountingCertificates.Batch011.certificate231 := by decide +kernel
theorem exponentialBound115 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate347).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate231).dm (WitnessCertificates.Batch011.certificate231).beta (WitnessCertificates.Batch011.certificate231).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate231).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch028.certificate347).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate231).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch028.certificate347 CountingCertificates.Batch011.certificate231 matches115 MergedCutGroups.Batch028.numericValid347 MergedCutGroups.Batch028.cellsSound347 MergedCutGroups.Batch028.cellsNumeric347 MergedCutGroups.Batch028.populationMatches347
    PopulationCertificates.Batch011.valid231 PopulationCertificates.Batch011.sound231 WitnessCertificates.Batch011.valid231 WitnessCertificates.Batch011.sound231 CountingCertificates.Batch011.valid231 CountingCertificates.Batch011.sound231 H st hI
theorem probabilityBound115 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate347).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate231).dm (WitnessCertificates.Batch011.certificate231).beta (WitnessCertificates.Batch011.certificate231).L) ≤ ((CutFailureCertificates.Budget011.certificate231).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound231 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate231).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate347).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate231).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate231).bound:ℝ) at hb
  exact (exponentialBound115 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches116 : (MergedCutGroups.Batch029.certificate350).AnchorMatches CountingCertificates.Batch011.certificate233 := by decide +kernel
theorem exponentialBound116 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate350).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate233).dm (WitnessCertificates.Batch011.certificate233).beta (WitnessCertificates.Batch011.certificate233).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate233).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch029.certificate350).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate233).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch029.certificate350 CountingCertificates.Batch011.certificate233 matches116 MergedCutGroups.Batch029.numericValid350 MergedCutGroups.Batch029.cellsSound350 MergedCutGroups.Batch029.cellsNumeric350 MergedCutGroups.Batch029.populationMatches350
    PopulationCertificates.Batch011.valid233 PopulationCertificates.Batch011.sound233 WitnessCertificates.Batch011.valid233 WitnessCertificates.Batch011.sound233 CountingCertificates.Batch011.valid233 CountingCertificates.Batch011.sound233 H st hI
theorem probabilityBound116 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate350).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate233).dm (WitnessCertificates.Batch011.certificate233).beta (WitnessCertificates.Batch011.certificate233).L) ≤ ((CutFailureCertificates.Budget011.certificate233).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound233 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate233).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate350).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate233).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate233).bound:ℝ) at hb
  exact (exponentialBound116 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches117 : (MergedCutGroups.Batch029.certificate353).AnchorMatches CountingCertificates.Batch011.certificate235 := by decide +kernel
theorem exponentialBound117 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate353).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate235).dm (WitnessCertificates.Batch011.certificate235).beta (WitnessCertificates.Batch011.certificate235).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate235).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch029.certificate353).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate235).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch029.certificate353 CountingCertificates.Batch011.certificate235 matches117 MergedCutGroups.Batch029.numericValid353 MergedCutGroups.Batch029.cellsSound353 MergedCutGroups.Batch029.cellsNumeric353 MergedCutGroups.Batch029.populationMatches353
    PopulationCertificates.Batch011.valid235 PopulationCertificates.Batch011.sound235 WitnessCertificates.Batch011.valid235 WitnessCertificates.Batch011.sound235 CountingCertificates.Batch011.valid235 CountingCertificates.Batch011.sound235 H st hI
theorem probabilityBound117 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate353).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate235).dm (WitnessCertificates.Batch011.certificate235).beta (WitnessCertificates.Batch011.certificate235).L) ≤ ((CutFailureCertificates.Budget011.certificate235).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound235 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate235).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate353).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate235).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate235).bound:ℝ) at hb
  exact (exponentialBound117 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches118 : (MergedCutGroups.Batch029.certificate356).AnchorMatches CountingCertificates.Batch011.certificate237 := by decide +kernel
theorem exponentialBound118 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate356).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate237).dm (WitnessCertificates.Batch011.certificate237).beta (WitnessCertificates.Batch011.certificate237).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate237).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch029.certificate356).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate237).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch029.certificate356 CountingCertificates.Batch011.certificate237 matches118 MergedCutGroups.Batch029.numericValid356 MergedCutGroups.Batch029.cellsSound356 MergedCutGroups.Batch029.cellsNumeric356 MergedCutGroups.Batch029.populationMatches356
    PopulationCertificates.Batch011.valid237 PopulationCertificates.Batch011.sound237 WitnessCertificates.Batch011.valid237 WitnessCertificates.Batch011.sound237 CountingCertificates.Batch011.valid237 CountingCertificates.Batch011.sound237 H st hI
theorem probabilityBound118 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate356).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate237).dm (WitnessCertificates.Batch011.certificate237).beta (WitnessCertificates.Batch011.certificate237).L) ≤ ((CutFailureCertificates.Budget011.certificate237).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound237 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate237).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate356).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate237).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate237).bound:ℝ) at hb
  exact (exponentialBound118 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches119 : (MergedCutGroups.Batch029.certificate359).AnchorMatches CountingCertificates.Batch011.certificate239 := by decide +kernel
theorem exponentialBound119 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate359).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate239).dm (WitnessCertificates.Batch011.certificate239).beta (WitnessCertificates.Batch011.certificate239).L) ≤ (2*exp (-((CountingCertificates.Batch011.certificate239).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch029.certificate359).exponent:ℝ)*st.R))/((WitnessCertificates.Batch011.certificate239).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch029.certificate359 CountingCertificates.Batch011.certificate239 matches119 MergedCutGroups.Batch029.numericValid359 MergedCutGroups.Batch029.cellsSound359 MergedCutGroups.Batch029.cellsNumeric359 MergedCutGroups.Batch029.populationMatches359
    PopulationCertificates.Batch011.valid239 PopulationCertificates.Batch011.sound239 WitnessCertificates.Batch011.valid239 WitnessCertificates.Batch011.sound239 CountingCertificates.Batch011.valid239 CountingCertificates.Batch011.sound239 H st hI
theorem probabilityBound119 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate359).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch011.certificate239).dm (WitnessCertificates.Batch011.certificate239).beta (WitnessCertificates.Batch011.certificate239).L) ≤ ((CutFailureCertificates.Budget011.certificate239).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound239 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate239).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate359).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch011.certificate239).omega:ℝ)) ≤ ((CutFailureCertificates.Budget011.certificate239).bound:ℝ) at hb
  exact (exponentialBound119 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch005
