import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch008
import Cycle12.CountingCertificates.Batch009
import Cycle12.CutFailureCertificates.Budget008
import Cycle12.CutFailureCertificates.Budget009
import Cycle12.CutLabelCertificates.Entropy004
import Cycle12.CutLabelCertificates.Entropy005
import Cycle12.CutLabelCertificates.Minority004
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

namespace Cycle12.CertifiedGlobalFailures.Batch004
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches80 : (MergedCutGroups.Batch020.certificate240).GlobalMatches MergedCutGroups.Batch020.certificate241 CountingCertificates.Batch008.certificate160 CutLabelCertificates.Entropy004.certificate81 CutLabelCertificates.Minority004.certificate80 := by decide +kernel
theorem exponentialBound80 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate240).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate160).dm (WitnessCertificates.Batch008.certificate160).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate160).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch020.certificate240).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch020.certificate241).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate160).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch020.certificate240 MergedCutGroups.Batch020.certificate241 CountingCertificates.Batch008.certificate160 CutLabelCertificates.Entropy004.certificate81 CutLabelCertificates.Minority004.certificate80 matches80 rfl rfl
    MergedCutGroups.Batch020.numericValid240 MergedCutGroups.Batch020.numericValid241 MergedCutGroups.Batch020.cellsSound240 MergedCutGroups.Batch020.cellsSound241
    MergedCutGroups.Batch020.cellsNumeric240 MergedCutGroups.Batch020.cellsNumeric241 MergedCutGroups.Batch020.populationMatches240 MergedCutGroups.Batch020.populationMatches241
    PopulationCertificates.Batch008.valid160 PopulationCertificates.Batch008.sound160 WitnessCertificates.Batch008.valid160 WitnessCertificates.Batch008.sound160 CountingCertificates.Batch008.valid160 CountingCertificates.Batch008.sound160
    CutLabelCertificates.Entropy004.valid81 CutLabelCertificates.Minority004.valid80 CutLabelCertificates.Minority004.sound80 H st hI
theorem probabilityBound80 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate240).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate160).dm (WitnessCertificates.Batch008.certificate160).beta) ≤ ((CutFailureCertificates.Budget008.certificate160).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound160 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate160).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate240).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate241).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate160).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate160).bound:ℝ) at hb
  exact (exponentialBound80 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches81 : (MergedCutGroups.Batch020.certificate243).GlobalMatches MergedCutGroups.Batch020.certificate244 CountingCertificates.Batch008.certificate162 CutLabelCertificates.Entropy004.certificate82 CutLabelCertificates.Minority004.certificate81 := by decide +kernel
theorem exponentialBound81 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate243).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate162).dm (WitnessCertificates.Batch008.certificate162).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate162).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch020.certificate243).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch020.certificate244).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate162).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch020.certificate243 MergedCutGroups.Batch020.certificate244 CountingCertificates.Batch008.certificate162 CutLabelCertificates.Entropy004.certificate82 CutLabelCertificates.Minority004.certificate81 matches81 rfl rfl
    MergedCutGroups.Batch020.numericValid243 MergedCutGroups.Batch020.numericValid244 MergedCutGroups.Batch020.cellsSound243 MergedCutGroups.Batch020.cellsSound244
    MergedCutGroups.Batch020.cellsNumeric243 MergedCutGroups.Batch020.cellsNumeric244 MergedCutGroups.Batch020.populationMatches243 MergedCutGroups.Batch020.populationMatches244
    PopulationCertificates.Batch008.valid162 PopulationCertificates.Batch008.sound162 WitnessCertificates.Batch008.valid162 WitnessCertificates.Batch008.sound162 CountingCertificates.Batch008.valid162 CountingCertificates.Batch008.sound162
    CutLabelCertificates.Entropy004.valid82 CutLabelCertificates.Minority004.valid81 CutLabelCertificates.Minority004.sound81 H st hI
theorem probabilityBound81 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate243).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate162).dm (WitnessCertificates.Batch008.certificate162).beta) ≤ ((CutFailureCertificates.Budget008.certificate162).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound162 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate162).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate243).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate244).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate162).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate162).bound:ℝ) at hb
  exact (exponentialBound81 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches82 : (MergedCutGroups.Batch020.certificate246).GlobalMatches MergedCutGroups.Batch020.certificate247 CountingCertificates.Batch008.certificate164 CutLabelCertificates.Entropy004.certificate83 CutLabelCertificates.Minority004.certificate82 := by decide +kernel
theorem exponentialBound82 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate246).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate164).dm (WitnessCertificates.Batch008.certificate164).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate164).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch020.certificate246).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch020.certificate247).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate164).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch020.certificate246 MergedCutGroups.Batch020.certificate247 CountingCertificates.Batch008.certificate164 CutLabelCertificates.Entropy004.certificate83 CutLabelCertificates.Minority004.certificate82 matches82 rfl rfl
    MergedCutGroups.Batch020.numericValid246 MergedCutGroups.Batch020.numericValid247 MergedCutGroups.Batch020.cellsSound246 MergedCutGroups.Batch020.cellsSound247
    MergedCutGroups.Batch020.cellsNumeric246 MergedCutGroups.Batch020.cellsNumeric247 MergedCutGroups.Batch020.populationMatches246 MergedCutGroups.Batch020.populationMatches247
    PopulationCertificates.Batch008.valid164 PopulationCertificates.Batch008.sound164 WitnessCertificates.Batch008.valid164 WitnessCertificates.Batch008.sound164 CountingCertificates.Batch008.valid164 CountingCertificates.Batch008.sound164
    CutLabelCertificates.Entropy004.valid83 CutLabelCertificates.Minority004.valid82 CutLabelCertificates.Minority004.sound82 H st hI
theorem probabilityBound82 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate246).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate164).dm (WitnessCertificates.Batch008.certificate164).beta) ≤ ((CutFailureCertificates.Budget008.certificate164).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound164 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate164).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate246).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate247).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate164).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate164).bound:ℝ) at hb
  exact (exponentialBound82 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches83 : (MergedCutGroups.Batch020.certificate249).GlobalMatches MergedCutGroups.Batch020.certificate250 CountingCertificates.Batch008.certificate166 CutLabelCertificates.Entropy004.certificate84 CutLabelCertificates.Minority004.certificate83 := by decide +kernel
theorem exponentialBound83 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate249).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate166).dm (WitnessCertificates.Batch008.certificate166).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate166).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch020.certificate249).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch020.certificate250).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate166).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch020.certificate249 MergedCutGroups.Batch020.certificate250 CountingCertificates.Batch008.certificate166 CutLabelCertificates.Entropy004.certificate84 CutLabelCertificates.Minority004.certificate83 matches83 rfl rfl
    MergedCutGroups.Batch020.numericValid249 MergedCutGroups.Batch020.numericValid250 MergedCutGroups.Batch020.cellsSound249 MergedCutGroups.Batch020.cellsSound250
    MergedCutGroups.Batch020.cellsNumeric249 MergedCutGroups.Batch020.cellsNumeric250 MergedCutGroups.Batch020.populationMatches249 MergedCutGroups.Batch020.populationMatches250
    PopulationCertificates.Batch008.valid166 PopulationCertificates.Batch008.sound166 WitnessCertificates.Batch008.valid166 WitnessCertificates.Batch008.sound166 CountingCertificates.Batch008.valid166 CountingCertificates.Batch008.sound166
    CutLabelCertificates.Entropy004.valid84 CutLabelCertificates.Minority004.valid83 CutLabelCertificates.Minority004.sound83 H st hI
theorem probabilityBound83 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate249).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate166).dm (WitnessCertificates.Batch008.certificate166).beta) ≤ ((CutFailureCertificates.Budget008.certificate166).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound166 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate166).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate249).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate250).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate166).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate166).bound:ℝ) at hb
  exact (exponentialBound83 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches84 : (MergedCutGroups.Batch021.certificate252).GlobalMatches MergedCutGroups.Batch021.certificate253 CountingCertificates.Batch008.certificate168 CutLabelCertificates.Entropy004.certificate85 CutLabelCertificates.Minority004.certificate84 := by decide +kernel
theorem exponentialBound84 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate252).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate168).dm (WitnessCertificates.Batch008.certificate168).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate168).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch021.certificate252).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch021.certificate253).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate168).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch021.certificate252 MergedCutGroups.Batch021.certificate253 CountingCertificates.Batch008.certificate168 CutLabelCertificates.Entropy004.certificate85 CutLabelCertificates.Minority004.certificate84 matches84 rfl rfl
    MergedCutGroups.Batch021.numericValid252 MergedCutGroups.Batch021.numericValid253 MergedCutGroups.Batch021.cellsSound252 MergedCutGroups.Batch021.cellsSound253
    MergedCutGroups.Batch021.cellsNumeric252 MergedCutGroups.Batch021.cellsNumeric253 MergedCutGroups.Batch021.populationMatches252 MergedCutGroups.Batch021.populationMatches253
    PopulationCertificates.Batch008.valid168 PopulationCertificates.Batch008.sound168 WitnessCertificates.Batch008.valid168 WitnessCertificates.Batch008.sound168 CountingCertificates.Batch008.valid168 CountingCertificates.Batch008.sound168
    CutLabelCertificates.Entropy004.valid85 CutLabelCertificates.Minority004.valid84 CutLabelCertificates.Minority004.sound84 H st hI
theorem probabilityBound84 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate252).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate168).dm (WitnessCertificates.Batch008.certificate168).beta) ≤ ((CutFailureCertificates.Budget008.certificate168).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound168 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate168).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate252).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate253).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate168).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate168).bound:ℝ) at hb
  exact (exponentialBound84 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches85 : (MergedCutGroups.Batch021.certificate255).GlobalMatches MergedCutGroups.Batch021.certificate256 CountingCertificates.Batch008.certificate170 CutLabelCertificates.Entropy004.certificate86 CutLabelCertificates.Minority004.certificate85 := by decide +kernel
theorem exponentialBound85 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate255).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate170).dm (WitnessCertificates.Batch008.certificate170).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate170).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch021.certificate255).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch021.certificate256).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate170).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch021.certificate255 MergedCutGroups.Batch021.certificate256 CountingCertificates.Batch008.certificate170 CutLabelCertificates.Entropy004.certificate86 CutLabelCertificates.Minority004.certificate85 matches85 rfl rfl
    MergedCutGroups.Batch021.numericValid255 MergedCutGroups.Batch021.numericValid256 MergedCutGroups.Batch021.cellsSound255 MergedCutGroups.Batch021.cellsSound256
    MergedCutGroups.Batch021.cellsNumeric255 MergedCutGroups.Batch021.cellsNumeric256 MergedCutGroups.Batch021.populationMatches255 MergedCutGroups.Batch021.populationMatches256
    PopulationCertificates.Batch008.valid170 PopulationCertificates.Batch008.sound170 WitnessCertificates.Batch008.valid170 WitnessCertificates.Batch008.sound170 CountingCertificates.Batch008.valid170 CountingCertificates.Batch008.sound170
    CutLabelCertificates.Entropy004.valid86 CutLabelCertificates.Minority004.valid85 CutLabelCertificates.Minority004.sound85 H st hI
theorem probabilityBound85 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate255).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate170).dm (WitnessCertificates.Batch008.certificate170).beta) ≤ ((CutFailureCertificates.Budget008.certificate170).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound170 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate170).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate255).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate256).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate170).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate170).bound:ℝ) at hb
  exact (exponentialBound85 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches86 : (MergedCutGroups.Batch021.certificate258).GlobalMatches MergedCutGroups.Batch021.certificate259 CountingCertificates.Batch008.certificate172 CutLabelCertificates.Entropy004.certificate87 CutLabelCertificates.Minority004.certificate86 := by decide +kernel
theorem exponentialBound86 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate258).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate172).dm (WitnessCertificates.Batch008.certificate172).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate172).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch021.certificate258).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch021.certificate259).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate172).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch021.certificate258 MergedCutGroups.Batch021.certificate259 CountingCertificates.Batch008.certificate172 CutLabelCertificates.Entropy004.certificate87 CutLabelCertificates.Minority004.certificate86 matches86 rfl rfl
    MergedCutGroups.Batch021.numericValid258 MergedCutGroups.Batch021.numericValid259 MergedCutGroups.Batch021.cellsSound258 MergedCutGroups.Batch021.cellsSound259
    MergedCutGroups.Batch021.cellsNumeric258 MergedCutGroups.Batch021.cellsNumeric259 MergedCutGroups.Batch021.populationMatches258 MergedCutGroups.Batch021.populationMatches259
    PopulationCertificates.Batch008.valid172 PopulationCertificates.Batch008.sound172 WitnessCertificates.Batch008.valid172 WitnessCertificates.Batch008.sound172 CountingCertificates.Batch008.valid172 CountingCertificates.Batch008.sound172
    CutLabelCertificates.Entropy004.valid87 CutLabelCertificates.Minority004.valid86 CutLabelCertificates.Minority004.sound86 H st hI
theorem probabilityBound86 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate258).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate172).dm (WitnessCertificates.Batch008.certificate172).beta) ≤ ((CutFailureCertificates.Budget008.certificate172).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound172 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate172).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate258).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate259).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate172).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate172).bound:ℝ) at hb
  exact (exponentialBound86 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches87 : (MergedCutGroups.Batch021.certificate261).GlobalMatches MergedCutGroups.Batch021.certificate262 CountingCertificates.Batch008.certificate174 CutLabelCertificates.Entropy004.certificate88 CutLabelCertificates.Minority004.certificate87 := by decide +kernel
theorem exponentialBound87 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate261).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate174).dm (WitnessCertificates.Batch008.certificate174).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate174).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch021.certificate261).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch021.certificate262).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate174).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch021.certificate261 MergedCutGroups.Batch021.certificate262 CountingCertificates.Batch008.certificate174 CutLabelCertificates.Entropy004.certificate88 CutLabelCertificates.Minority004.certificate87 matches87 rfl rfl
    MergedCutGroups.Batch021.numericValid261 MergedCutGroups.Batch021.numericValid262 MergedCutGroups.Batch021.cellsSound261 MergedCutGroups.Batch021.cellsSound262
    MergedCutGroups.Batch021.cellsNumeric261 MergedCutGroups.Batch021.cellsNumeric262 MergedCutGroups.Batch021.populationMatches261 MergedCutGroups.Batch021.populationMatches262
    PopulationCertificates.Batch008.valid174 PopulationCertificates.Batch008.sound174 WitnessCertificates.Batch008.valid174 WitnessCertificates.Batch008.sound174 CountingCertificates.Batch008.valid174 CountingCertificates.Batch008.sound174
    CutLabelCertificates.Entropy004.valid88 CutLabelCertificates.Minority004.valid87 CutLabelCertificates.Minority004.sound87 H st hI
theorem probabilityBound87 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate261).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate174).dm (WitnessCertificates.Batch008.certificate174).beta) ≤ ((CutFailureCertificates.Budget008.certificate174).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound174 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate174).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate261).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate262).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate174).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate174).bound:ℝ) at hb
  exact (exponentialBound87 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches88 : (MergedCutGroups.Batch022.certificate264).GlobalMatches MergedCutGroups.Batch022.certificate265 CountingCertificates.Batch008.certificate176 CutLabelCertificates.Entropy004.certificate89 CutLabelCertificates.Minority004.certificate88 := by decide +kernel
theorem exponentialBound88 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate264).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate176).dm (WitnessCertificates.Batch008.certificate176).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate176).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch022.certificate264).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch022.certificate265).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate176).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch022.certificate264 MergedCutGroups.Batch022.certificate265 CountingCertificates.Batch008.certificate176 CutLabelCertificates.Entropy004.certificate89 CutLabelCertificates.Minority004.certificate88 matches88 rfl rfl
    MergedCutGroups.Batch022.numericValid264 MergedCutGroups.Batch022.numericValid265 MergedCutGroups.Batch022.cellsSound264 MergedCutGroups.Batch022.cellsSound265
    MergedCutGroups.Batch022.cellsNumeric264 MergedCutGroups.Batch022.cellsNumeric265 MergedCutGroups.Batch022.populationMatches264 MergedCutGroups.Batch022.populationMatches265
    PopulationCertificates.Batch008.valid176 PopulationCertificates.Batch008.sound176 WitnessCertificates.Batch008.valid176 WitnessCertificates.Batch008.sound176 CountingCertificates.Batch008.valid176 CountingCertificates.Batch008.sound176
    CutLabelCertificates.Entropy004.valid89 CutLabelCertificates.Minority004.valid88 CutLabelCertificates.Minority004.sound88 H st hI
theorem probabilityBound88 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate264).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate176).dm (WitnessCertificates.Batch008.certificate176).beta) ≤ ((CutFailureCertificates.Budget008.certificate176).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound176 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate176).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate264).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate265).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate176).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate176).bound:ℝ) at hb
  exact (exponentialBound88 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches89 : (MergedCutGroups.Batch022.certificate267).GlobalMatches MergedCutGroups.Batch022.certificate268 CountingCertificates.Batch008.certificate178 CutLabelCertificates.Entropy004.certificate90 CutLabelCertificates.Minority004.certificate89 := by decide +kernel
theorem exponentialBound89 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate267).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate178).dm (WitnessCertificates.Batch008.certificate178).beta) ≤ (2*exp (-((CountingCertificates.Batch008.certificate178).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch022.certificate267).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch022.certificate268).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch008.certificate178).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch022.certificate267 MergedCutGroups.Batch022.certificate268 CountingCertificates.Batch008.certificate178 CutLabelCertificates.Entropy004.certificate90 CutLabelCertificates.Minority004.certificate89 matches89 rfl rfl
    MergedCutGroups.Batch022.numericValid267 MergedCutGroups.Batch022.numericValid268 MergedCutGroups.Batch022.cellsSound267 MergedCutGroups.Batch022.cellsSound268
    MergedCutGroups.Batch022.cellsNumeric267 MergedCutGroups.Batch022.cellsNumeric268 MergedCutGroups.Batch022.populationMatches267 MergedCutGroups.Batch022.populationMatches268
    PopulationCertificates.Batch008.valid178 PopulationCertificates.Batch008.sound178 WitnessCertificates.Batch008.valid178 WitnessCertificates.Batch008.sound178 CountingCertificates.Batch008.valid178 CountingCertificates.Batch008.sound178
    CutLabelCertificates.Entropy004.valid90 CutLabelCertificates.Minority004.valid89 CutLabelCertificates.Minority004.sound89 H st hI
theorem probabilityBound89 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate267).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch008.certificate178).dm (WitnessCertificates.Batch008.certificate178).beta) ≤ ((CutFailureCertificates.Budget008.certificate178).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound178 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate178).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate267).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate268).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch008.certificate178).omega:ℝ) ≤ ((CutFailureCertificates.Budget008.certificate178).bound:ℝ) at hb
  exact (exponentialBound89 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches90 : (MergedCutGroups.Batch022.certificate270).GlobalMatches MergedCutGroups.Batch022.certificate271 CountingCertificates.Batch009.certificate180 CutLabelCertificates.Entropy004.certificate91 CutLabelCertificates.Minority004.certificate90 := by decide +kernel
theorem exponentialBound90 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate270).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate180).dm (WitnessCertificates.Batch009.certificate180).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate180).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch022.certificate270).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch022.certificate271).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate180).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch022.certificate270 MergedCutGroups.Batch022.certificate271 CountingCertificates.Batch009.certificate180 CutLabelCertificates.Entropy004.certificate91 CutLabelCertificates.Minority004.certificate90 matches90 rfl rfl
    MergedCutGroups.Batch022.numericValid270 MergedCutGroups.Batch022.numericValid271 MergedCutGroups.Batch022.cellsSound270 MergedCutGroups.Batch022.cellsSound271
    MergedCutGroups.Batch022.cellsNumeric270 MergedCutGroups.Batch022.cellsNumeric271 MergedCutGroups.Batch022.populationMatches270 MergedCutGroups.Batch022.populationMatches271
    PopulationCertificates.Batch009.valid180 PopulationCertificates.Batch009.sound180 WitnessCertificates.Batch009.valid180 WitnessCertificates.Batch009.sound180 CountingCertificates.Batch009.valid180 CountingCertificates.Batch009.sound180
    CutLabelCertificates.Entropy004.valid91 CutLabelCertificates.Minority004.valid90 CutLabelCertificates.Minority004.sound90 H st hI
theorem probabilityBound90 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate270).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate180).dm (WitnessCertificates.Batch009.certificate180).beta) ≤ ((CutFailureCertificates.Budget009.certificate180).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound180 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate180).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate270).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate271).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate180).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate180).bound:ℝ) at hb
  exact (exponentialBound90 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches91 : (MergedCutGroups.Batch022.certificate273).GlobalMatches MergedCutGroups.Batch022.certificate274 CountingCertificates.Batch009.certificate182 CutLabelCertificates.Entropy004.certificate92 CutLabelCertificates.Minority004.certificate91 := by decide +kernel
theorem exponentialBound91 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate273).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate182).dm (WitnessCertificates.Batch009.certificate182).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate182).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch022.certificate273).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch022.certificate274).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate182).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch022.certificate273 MergedCutGroups.Batch022.certificate274 CountingCertificates.Batch009.certificate182 CutLabelCertificates.Entropy004.certificate92 CutLabelCertificates.Minority004.certificate91 matches91 rfl rfl
    MergedCutGroups.Batch022.numericValid273 MergedCutGroups.Batch022.numericValid274 MergedCutGroups.Batch022.cellsSound273 MergedCutGroups.Batch022.cellsSound274
    MergedCutGroups.Batch022.cellsNumeric273 MergedCutGroups.Batch022.cellsNumeric274 MergedCutGroups.Batch022.populationMatches273 MergedCutGroups.Batch022.populationMatches274
    PopulationCertificates.Batch009.valid182 PopulationCertificates.Batch009.sound182 WitnessCertificates.Batch009.valid182 WitnessCertificates.Batch009.sound182 CountingCertificates.Batch009.valid182 CountingCertificates.Batch009.sound182
    CutLabelCertificates.Entropy004.valid92 CutLabelCertificates.Minority004.valid91 CutLabelCertificates.Minority004.sound91 H st hI
theorem probabilityBound91 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate273).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate182).dm (WitnessCertificates.Batch009.certificate182).beta) ≤ ((CutFailureCertificates.Budget009.certificate182).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound182 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate182).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate273).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate274).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate182).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate182).bound:ℝ) at hb
  exact (exponentialBound91 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches92 : (MergedCutGroups.Batch023.certificate276).GlobalMatches MergedCutGroups.Batch023.certificate277 CountingCertificates.Batch009.certificate184 CutLabelCertificates.Entropy004.certificate93 CutLabelCertificates.Minority004.certificate92 := by decide +kernel
theorem exponentialBound92 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate276).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate184).dm (WitnessCertificates.Batch009.certificate184).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate184).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch023.certificate276).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch023.certificate277).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate184).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch023.certificate276 MergedCutGroups.Batch023.certificate277 CountingCertificates.Batch009.certificate184 CutLabelCertificates.Entropy004.certificate93 CutLabelCertificates.Minority004.certificate92 matches92 rfl rfl
    MergedCutGroups.Batch023.numericValid276 MergedCutGroups.Batch023.numericValid277 MergedCutGroups.Batch023.cellsSound276 MergedCutGroups.Batch023.cellsSound277
    MergedCutGroups.Batch023.cellsNumeric276 MergedCutGroups.Batch023.cellsNumeric277 MergedCutGroups.Batch023.populationMatches276 MergedCutGroups.Batch023.populationMatches277
    PopulationCertificates.Batch009.valid184 PopulationCertificates.Batch009.sound184 WitnessCertificates.Batch009.valid184 WitnessCertificates.Batch009.sound184 CountingCertificates.Batch009.valid184 CountingCertificates.Batch009.sound184
    CutLabelCertificates.Entropy004.valid93 CutLabelCertificates.Minority004.valid92 CutLabelCertificates.Minority004.sound92 H st hI
theorem probabilityBound92 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate276).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate184).dm (WitnessCertificates.Batch009.certificate184).beta) ≤ ((CutFailureCertificates.Budget009.certificate184).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound184 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate184).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate276).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate277).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate184).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate184).bound:ℝ) at hb
  exact (exponentialBound92 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches93 : (MergedCutGroups.Batch023.certificate279).GlobalMatches MergedCutGroups.Batch023.certificate280 CountingCertificates.Batch009.certificate186 CutLabelCertificates.Entropy004.certificate94 CutLabelCertificates.Minority004.certificate93 := by decide +kernel
theorem exponentialBound93 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate279).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate186).dm (WitnessCertificates.Batch009.certificate186).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate186).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch023.certificate279).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch023.certificate280).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate186).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch023.certificate279 MergedCutGroups.Batch023.certificate280 CountingCertificates.Batch009.certificate186 CutLabelCertificates.Entropy004.certificate94 CutLabelCertificates.Minority004.certificate93 matches93 rfl rfl
    MergedCutGroups.Batch023.numericValid279 MergedCutGroups.Batch023.numericValid280 MergedCutGroups.Batch023.cellsSound279 MergedCutGroups.Batch023.cellsSound280
    MergedCutGroups.Batch023.cellsNumeric279 MergedCutGroups.Batch023.cellsNumeric280 MergedCutGroups.Batch023.populationMatches279 MergedCutGroups.Batch023.populationMatches280
    PopulationCertificates.Batch009.valid186 PopulationCertificates.Batch009.sound186 WitnessCertificates.Batch009.valid186 WitnessCertificates.Batch009.sound186 CountingCertificates.Batch009.valid186 CountingCertificates.Batch009.sound186
    CutLabelCertificates.Entropy004.valid94 CutLabelCertificates.Minority004.valid93 CutLabelCertificates.Minority004.sound93 H st hI
theorem probabilityBound93 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate279).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate186).dm (WitnessCertificates.Batch009.certificate186).beta) ≤ ((CutFailureCertificates.Budget009.certificate186).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound186 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate186).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate279).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate280).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate186).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate186).bound:ℝ) at hb
  exact (exponentialBound93 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches94 : (MergedCutGroups.Batch023.certificate282).GlobalMatches MergedCutGroups.Batch023.certificate283 CountingCertificates.Batch009.certificate188 CutLabelCertificates.Entropy004.certificate95 CutLabelCertificates.Minority004.certificate94 := by decide +kernel
theorem exponentialBound94 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate282).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate188).dm (WitnessCertificates.Batch009.certificate188).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate188).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch023.certificate282).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch023.certificate283).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate188).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch023.certificate282 MergedCutGroups.Batch023.certificate283 CountingCertificates.Batch009.certificate188 CutLabelCertificates.Entropy004.certificate95 CutLabelCertificates.Minority004.certificate94 matches94 rfl rfl
    MergedCutGroups.Batch023.numericValid282 MergedCutGroups.Batch023.numericValid283 MergedCutGroups.Batch023.cellsSound282 MergedCutGroups.Batch023.cellsSound283
    MergedCutGroups.Batch023.cellsNumeric282 MergedCutGroups.Batch023.cellsNumeric283 MergedCutGroups.Batch023.populationMatches282 MergedCutGroups.Batch023.populationMatches283
    PopulationCertificates.Batch009.valid188 PopulationCertificates.Batch009.sound188 WitnessCertificates.Batch009.valid188 WitnessCertificates.Batch009.sound188 CountingCertificates.Batch009.valid188 CountingCertificates.Batch009.sound188
    CutLabelCertificates.Entropy004.valid95 CutLabelCertificates.Minority004.valid94 CutLabelCertificates.Minority004.sound94 H st hI
theorem probabilityBound94 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate282).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate188).dm (WitnessCertificates.Batch009.certificate188).beta) ≤ ((CutFailureCertificates.Budget009.certificate188).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound188 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate188).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate282).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate283).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate188).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate188).bound:ℝ) at hb
  exact (exponentialBound94 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches95 : (MergedCutGroups.Batch023.certificate285).GlobalMatches MergedCutGroups.Batch023.certificate286 CountingCertificates.Batch009.certificate190 CutLabelCertificates.Entropy004.certificate96 CutLabelCertificates.Minority004.certificate95 := by decide +kernel
theorem exponentialBound95 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate285).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate190).dm (WitnessCertificates.Batch009.certificate190).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate190).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch023.certificate285).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch023.certificate286).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate190).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch023.certificate285 MergedCutGroups.Batch023.certificate286 CountingCertificates.Batch009.certificate190 CutLabelCertificates.Entropy004.certificate96 CutLabelCertificates.Minority004.certificate95 matches95 rfl rfl
    MergedCutGroups.Batch023.numericValid285 MergedCutGroups.Batch023.numericValid286 MergedCutGroups.Batch023.cellsSound285 MergedCutGroups.Batch023.cellsSound286
    MergedCutGroups.Batch023.cellsNumeric285 MergedCutGroups.Batch023.cellsNumeric286 MergedCutGroups.Batch023.populationMatches285 MergedCutGroups.Batch023.populationMatches286
    PopulationCertificates.Batch009.valid190 PopulationCertificates.Batch009.sound190 WitnessCertificates.Batch009.valid190 WitnessCertificates.Batch009.sound190 CountingCertificates.Batch009.valid190 CountingCertificates.Batch009.sound190
    CutLabelCertificates.Entropy004.valid96 CutLabelCertificates.Minority004.valid95 CutLabelCertificates.Minority004.sound95 H st hI
theorem probabilityBound95 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate285).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate190).dm (WitnessCertificates.Batch009.certificate190).beta) ≤ ((CutFailureCertificates.Budget009.certificate190).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound190 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate190).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate285).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate286).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate190).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate190).bound:ℝ) at hb
  exact (exponentialBound95 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches96 : (MergedCutGroups.Batch024.certificate288).GlobalMatches MergedCutGroups.Batch024.certificate289 CountingCertificates.Batch009.certificate192 CutLabelCertificates.Entropy004.certificate97 CutLabelCertificates.Minority004.certificate96 := by decide +kernel
theorem exponentialBound96 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate288).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate192).dm (WitnessCertificates.Batch009.certificate192).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate192).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch024.certificate288).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch024.certificate289).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate192).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch024.certificate288 MergedCutGroups.Batch024.certificate289 CountingCertificates.Batch009.certificate192 CutLabelCertificates.Entropy004.certificate97 CutLabelCertificates.Minority004.certificate96 matches96 rfl rfl
    MergedCutGroups.Batch024.numericValid288 MergedCutGroups.Batch024.numericValid289 MergedCutGroups.Batch024.cellsSound288 MergedCutGroups.Batch024.cellsSound289
    MergedCutGroups.Batch024.cellsNumeric288 MergedCutGroups.Batch024.cellsNumeric289 MergedCutGroups.Batch024.populationMatches288 MergedCutGroups.Batch024.populationMatches289
    PopulationCertificates.Batch009.valid192 PopulationCertificates.Batch009.sound192 WitnessCertificates.Batch009.valid192 WitnessCertificates.Batch009.sound192 CountingCertificates.Batch009.valid192 CountingCertificates.Batch009.sound192
    CutLabelCertificates.Entropy004.valid97 CutLabelCertificates.Minority004.valid96 CutLabelCertificates.Minority004.sound96 H st hI
theorem probabilityBound96 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate288).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate192).dm (WitnessCertificates.Batch009.certificate192).beta) ≤ ((CutFailureCertificates.Budget009.certificate192).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound192 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate192).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate288).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate289).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate192).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate192).bound:ℝ) at hb
  exact (exponentialBound96 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches97 : (MergedCutGroups.Batch024.certificate291).GlobalMatches MergedCutGroups.Batch024.certificate292 CountingCertificates.Batch009.certificate194 CutLabelCertificates.Entropy004.certificate98 CutLabelCertificates.Minority004.certificate97 := by decide +kernel
theorem exponentialBound97 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate291).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate194).dm (WitnessCertificates.Batch009.certificate194).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate194).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch024.certificate291).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch024.certificate292).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate194).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch024.certificate291 MergedCutGroups.Batch024.certificate292 CountingCertificates.Batch009.certificate194 CutLabelCertificates.Entropy004.certificate98 CutLabelCertificates.Minority004.certificate97 matches97 rfl rfl
    MergedCutGroups.Batch024.numericValid291 MergedCutGroups.Batch024.numericValid292 MergedCutGroups.Batch024.cellsSound291 MergedCutGroups.Batch024.cellsSound292
    MergedCutGroups.Batch024.cellsNumeric291 MergedCutGroups.Batch024.cellsNumeric292 MergedCutGroups.Batch024.populationMatches291 MergedCutGroups.Batch024.populationMatches292
    PopulationCertificates.Batch009.valid194 PopulationCertificates.Batch009.sound194 WitnessCertificates.Batch009.valid194 WitnessCertificates.Batch009.sound194 CountingCertificates.Batch009.valid194 CountingCertificates.Batch009.sound194
    CutLabelCertificates.Entropy004.valid98 CutLabelCertificates.Minority004.valid97 CutLabelCertificates.Minority004.sound97 H st hI
theorem probabilityBound97 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate291).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate194).dm (WitnessCertificates.Batch009.certificate194).beta) ≤ ((CutFailureCertificates.Budget009.certificate194).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound194 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate194).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate291).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate292).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate194).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate194).bound:ℝ) at hb
  exact (exponentialBound97 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches98 : (MergedCutGroups.Batch024.certificate294).GlobalMatches MergedCutGroups.Batch024.certificate295 CountingCertificates.Batch009.certificate196 CutLabelCertificates.Entropy004.certificate99 CutLabelCertificates.Minority004.certificate98 := by decide +kernel
theorem exponentialBound98 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate294).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate196).dm (WitnessCertificates.Batch009.certificate196).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate196).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch024.certificate294).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch024.certificate295).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate196).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch024.certificate294 MergedCutGroups.Batch024.certificate295 CountingCertificates.Batch009.certificate196 CutLabelCertificates.Entropy004.certificate99 CutLabelCertificates.Minority004.certificate98 matches98 rfl rfl
    MergedCutGroups.Batch024.numericValid294 MergedCutGroups.Batch024.numericValid295 MergedCutGroups.Batch024.cellsSound294 MergedCutGroups.Batch024.cellsSound295
    MergedCutGroups.Batch024.cellsNumeric294 MergedCutGroups.Batch024.cellsNumeric295 MergedCutGroups.Batch024.populationMatches294 MergedCutGroups.Batch024.populationMatches295
    PopulationCertificates.Batch009.valid196 PopulationCertificates.Batch009.sound196 WitnessCertificates.Batch009.valid196 WitnessCertificates.Batch009.sound196 CountingCertificates.Batch009.valid196 CountingCertificates.Batch009.sound196
    CutLabelCertificates.Entropy004.valid99 CutLabelCertificates.Minority004.valid98 CutLabelCertificates.Minority004.sound98 H st hI
theorem probabilityBound98 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate294).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate196).dm (WitnessCertificates.Batch009.certificate196).beta) ≤ ((CutFailureCertificates.Budget009.certificate196).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound196 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate196).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate294).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate295).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate196).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate196).bound:ℝ) at hb
  exact (exponentialBound98 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches99 : (MergedCutGroups.Batch024.certificate297).GlobalMatches MergedCutGroups.Batch024.certificate298 CountingCertificates.Batch009.certificate198 CutLabelCertificates.Entropy005.certificate100 CutLabelCertificates.Minority004.certificate99 := by decide +kernel
theorem exponentialBound99 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate297).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate198).dm (WitnessCertificates.Batch009.certificate198).beta) ≤ (2*exp (-((CountingCertificates.Batch009.certificate198).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch024.certificate297).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch024.certificate298).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch009.certificate198).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch024.certificate297 MergedCutGroups.Batch024.certificate298 CountingCertificates.Batch009.certificate198 CutLabelCertificates.Entropy005.certificate100 CutLabelCertificates.Minority004.certificate99 matches99 rfl rfl
    MergedCutGroups.Batch024.numericValid297 MergedCutGroups.Batch024.numericValid298 MergedCutGroups.Batch024.cellsSound297 MergedCutGroups.Batch024.cellsSound298
    MergedCutGroups.Batch024.cellsNumeric297 MergedCutGroups.Batch024.cellsNumeric298 MergedCutGroups.Batch024.populationMatches297 MergedCutGroups.Batch024.populationMatches298
    PopulationCertificates.Batch009.valid198 PopulationCertificates.Batch009.sound198 WitnessCertificates.Batch009.valid198 WitnessCertificates.Batch009.sound198 CountingCertificates.Batch009.valid198 CountingCertificates.Batch009.sound198
    CutLabelCertificates.Entropy005.valid100 CutLabelCertificates.Minority004.valid99 CutLabelCertificates.Minority004.sound99 H st hI
theorem probabilityBound99 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate297).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch009.certificate198).dm (WitnessCertificates.Batch009.certificate198).beta) ≤ ((CutFailureCertificates.Budget009.certificate198).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound198 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate198).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate297).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate298).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch009.certificate198).omega:ℝ) ≤ ((CutFailureCertificates.Budget009.certificate198).bound:ℝ) at hb
  exact (exponentialBound99 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch004
