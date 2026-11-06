import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch010
import Cycle12.CountingCertificates.Batch011
import Cycle12.CutFailureCertificates.Budget010
import Cycle12.CutFailureCertificates.Budget011
import Cycle12.CutLabelCertificates.Entropy005
import Cycle12.CutLabelCertificates.Entropy006
import Cycle12.CutLabelCertificates.Minority005
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

namespace Cycle12.CertifiedGlobalFailures.Batch005
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches100 : (MergedCutGroups.Batch025.certificate300).GlobalMatches MergedCutGroups.Batch025.certificate301 CountingCertificates.Batch010.certificate200 CutLabelCertificates.Entropy005.certificate101 CutLabelCertificates.Minority005.certificate100 := by decide +kernel
theorem exponentialBound100 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate300).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate200).dm (WitnessCertificates.Batch010.certificate200).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate200).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch025.certificate300).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch025.certificate301).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate200).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch025.certificate300 MergedCutGroups.Batch025.certificate301 CountingCertificates.Batch010.certificate200 CutLabelCertificates.Entropy005.certificate101 CutLabelCertificates.Minority005.certificate100 matches100 rfl rfl
    MergedCutGroups.Batch025.numericValid300 MergedCutGroups.Batch025.numericValid301 MergedCutGroups.Batch025.cellsSound300 MergedCutGroups.Batch025.cellsSound301
    MergedCutGroups.Batch025.cellsNumeric300 MergedCutGroups.Batch025.cellsNumeric301 MergedCutGroups.Batch025.populationMatches300 MergedCutGroups.Batch025.populationMatches301
    PopulationCertificates.Batch010.valid200 PopulationCertificates.Batch010.sound200 WitnessCertificates.Batch010.valid200 WitnessCertificates.Batch010.sound200 CountingCertificates.Batch010.valid200 CountingCertificates.Batch010.sound200
    CutLabelCertificates.Entropy005.valid101 CutLabelCertificates.Minority005.valid100 CutLabelCertificates.Minority005.sound100 H st hI
theorem probabilityBound100 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate300).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate200).dm (WitnessCertificates.Batch010.certificate200).beta) ≤ ((CutFailureCertificates.Budget010.certificate200).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound200 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate200).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate300).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate301).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate200).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate200).bound:ℝ) at hb
  exact (exponentialBound100 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches101 : (MergedCutGroups.Batch025.certificate303).GlobalMatches MergedCutGroups.Batch025.certificate304 CountingCertificates.Batch010.certificate202 CutLabelCertificates.Entropy005.certificate102 CutLabelCertificates.Minority005.certificate101 := by decide +kernel
theorem exponentialBound101 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate303).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate202).dm (WitnessCertificates.Batch010.certificate202).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate202).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch025.certificate303).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch025.certificate304).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate202).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch025.certificate303 MergedCutGroups.Batch025.certificate304 CountingCertificates.Batch010.certificate202 CutLabelCertificates.Entropy005.certificate102 CutLabelCertificates.Minority005.certificate101 matches101 rfl rfl
    MergedCutGroups.Batch025.numericValid303 MergedCutGroups.Batch025.numericValid304 MergedCutGroups.Batch025.cellsSound303 MergedCutGroups.Batch025.cellsSound304
    MergedCutGroups.Batch025.cellsNumeric303 MergedCutGroups.Batch025.cellsNumeric304 MergedCutGroups.Batch025.populationMatches303 MergedCutGroups.Batch025.populationMatches304
    PopulationCertificates.Batch010.valid202 PopulationCertificates.Batch010.sound202 WitnessCertificates.Batch010.valid202 WitnessCertificates.Batch010.sound202 CountingCertificates.Batch010.valid202 CountingCertificates.Batch010.sound202
    CutLabelCertificates.Entropy005.valid102 CutLabelCertificates.Minority005.valid101 CutLabelCertificates.Minority005.sound101 H st hI
theorem probabilityBound101 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate303).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate202).dm (WitnessCertificates.Batch010.certificate202).beta) ≤ ((CutFailureCertificates.Budget010.certificate202).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound202 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate202).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate303).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate304).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate202).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate202).bound:ℝ) at hb
  exact (exponentialBound101 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches102 : (MergedCutGroups.Batch025.certificate306).GlobalMatches MergedCutGroups.Batch025.certificate307 CountingCertificates.Batch010.certificate204 CutLabelCertificates.Entropy005.certificate103 CutLabelCertificates.Minority005.certificate102 := by decide +kernel
theorem exponentialBound102 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate306).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate204).dm (WitnessCertificates.Batch010.certificate204).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate204).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch025.certificate306).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch025.certificate307).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate204).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch025.certificate306 MergedCutGroups.Batch025.certificate307 CountingCertificates.Batch010.certificate204 CutLabelCertificates.Entropy005.certificate103 CutLabelCertificates.Minority005.certificate102 matches102 rfl rfl
    MergedCutGroups.Batch025.numericValid306 MergedCutGroups.Batch025.numericValid307 MergedCutGroups.Batch025.cellsSound306 MergedCutGroups.Batch025.cellsSound307
    MergedCutGroups.Batch025.cellsNumeric306 MergedCutGroups.Batch025.cellsNumeric307 MergedCutGroups.Batch025.populationMatches306 MergedCutGroups.Batch025.populationMatches307
    PopulationCertificates.Batch010.valid204 PopulationCertificates.Batch010.sound204 WitnessCertificates.Batch010.valid204 WitnessCertificates.Batch010.sound204 CountingCertificates.Batch010.valid204 CountingCertificates.Batch010.sound204
    CutLabelCertificates.Entropy005.valid103 CutLabelCertificates.Minority005.valid102 CutLabelCertificates.Minority005.sound102 H st hI
theorem probabilityBound102 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate306).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate204).dm (WitnessCertificates.Batch010.certificate204).beta) ≤ ((CutFailureCertificates.Budget010.certificate204).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound204 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate204).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate306).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate307).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate204).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate204).bound:ℝ) at hb
  exact (exponentialBound102 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches103 : (MergedCutGroups.Batch025.certificate309).GlobalMatches MergedCutGroups.Batch025.certificate310 CountingCertificates.Batch010.certificate206 CutLabelCertificates.Entropy005.certificate104 CutLabelCertificates.Minority005.certificate103 := by decide +kernel
theorem exponentialBound103 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate309).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate206).dm (WitnessCertificates.Batch010.certificate206).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate206).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch025.certificate309).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch025.certificate310).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate206).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch025.certificate309 MergedCutGroups.Batch025.certificate310 CountingCertificates.Batch010.certificate206 CutLabelCertificates.Entropy005.certificate104 CutLabelCertificates.Minority005.certificate103 matches103 rfl rfl
    MergedCutGroups.Batch025.numericValid309 MergedCutGroups.Batch025.numericValid310 MergedCutGroups.Batch025.cellsSound309 MergedCutGroups.Batch025.cellsSound310
    MergedCutGroups.Batch025.cellsNumeric309 MergedCutGroups.Batch025.cellsNumeric310 MergedCutGroups.Batch025.populationMatches309 MergedCutGroups.Batch025.populationMatches310
    PopulationCertificates.Batch010.valid206 PopulationCertificates.Batch010.sound206 WitnessCertificates.Batch010.valid206 WitnessCertificates.Batch010.sound206 CountingCertificates.Batch010.valid206 CountingCertificates.Batch010.sound206
    CutLabelCertificates.Entropy005.valid104 CutLabelCertificates.Minority005.valid103 CutLabelCertificates.Minority005.sound103 H st hI
theorem probabilityBound103 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch025.certificate309).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate206).dm (WitnessCertificates.Batch010.certificate206).beta) ≤ ((CutFailureCertificates.Budget010.certificate206).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound206 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate206).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate309).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch025.certificate310).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate206).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate206).bound:ℝ) at hb
  exact (exponentialBound103 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches104 : (MergedCutGroups.Batch026.certificate312).GlobalMatches MergedCutGroups.Batch026.certificate313 CountingCertificates.Batch010.certificate208 CutLabelCertificates.Entropy005.certificate105 CutLabelCertificates.Minority005.certificate104 := by decide +kernel
theorem exponentialBound104 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate312).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate208).dm (WitnessCertificates.Batch010.certificate208).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate208).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch026.certificate312).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch026.certificate313).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate208).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch026.certificate312 MergedCutGroups.Batch026.certificate313 CountingCertificates.Batch010.certificate208 CutLabelCertificates.Entropy005.certificate105 CutLabelCertificates.Minority005.certificate104 matches104 rfl rfl
    MergedCutGroups.Batch026.numericValid312 MergedCutGroups.Batch026.numericValid313 MergedCutGroups.Batch026.cellsSound312 MergedCutGroups.Batch026.cellsSound313
    MergedCutGroups.Batch026.cellsNumeric312 MergedCutGroups.Batch026.cellsNumeric313 MergedCutGroups.Batch026.populationMatches312 MergedCutGroups.Batch026.populationMatches313
    PopulationCertificates.Batch010.valid208 PopulationCertificates.Batch010.sound208 WitnessCertificates.Batch010.valid208 WitnessCertificates.Batch010.sound208 CountingCertificates.Batch010.valid208 CountingCertificates.Batch010.sound208
    CutLabelCertificates.Entropy005.valid105 CutLabelCertificates.Minority005.valid104 CutLabelCertificates.Minority005.sound104 H st hI
theorem probabilityBound104 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate312).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate208).dm (WitnessCertificates.Batch010.certificate208).beta) ≤ ((CutFailureCertificates.Budget010.certificate208).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound208 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate208).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate312).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate313).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate208).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate208).bound:ℝ) at hb
  exact (exponentialBound104 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches105 : (MergedCutGroups.Batch026.certificate315).GlobalMatches MergedCutGroups.Batch026.certificate316 CountingCertificates.Batch010.certificate210 CutLabelCertificates.Entropy005.certificate106 CutLabelCertificates.Minority005.certificate105 := by decide +kernel
theorem exponentialBound105 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate315).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate210).dm (WitnessCertificates.Batch010.certificate210).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate210).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch026.certificate315).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch026.certificate316).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate210).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch026.certificate315 MergedCutGroups.Batch026.certificate316 CountingCertificates.Batch010.certificate210 CutLabelCertificates.Entropy005.certificate106 CutLabelCertificates.Minority005.certificate105 matches105 rfl rfl
    MergedCutGroups.Batch026.numericValid315 MergedCutGroups.Batch026.numericValid316 MergedCutGroups.Batch026.cellsSound315 MergedCutGroups.Batch026.cellsSound316
    MergedCutGroups.Batch026.cellsNumeric315 MergedCutGroups.Batch026.cellsNumeric316 MergedCutGroups.Batch026.populationMatches315 MergedCutGroups.Batch026.populationMatches316
    PopulationCertificates.Batch010.valid210 PopulationCertificates.Batch010.sound210 WitnessCertificates.Batch010.valid210 WitnessCertificates.Batch010.sound210 CountingCertificates.Batch010.valid210 CountingCertificates.Batch010.sound210
    CutLabelCertificates.Entropy005.valid106 CutLabelCertificates.Minority005.valid105 CutLabelCertificates.Minority005.sound105 H st hI
theorem probabilityBound105 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate315).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate210).dm (WitnessCertificates.Batch010.certificate210).beta) ≤ ((CutFailureCertificates.Budget010.certificate210).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound210 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate210).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate315).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate316).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate210).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate210).bound:ℝ) at hb
  exact (exponentialBound105 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches106 : (MergedCutGroups.Batch026.certificate318).GlobalMatches MergedCutGroups.Batch026.certificate319 CountingCertificates.Batch010.certificate212 CutLabelCertificates.Entropy005.certificate107 CutLabelCertificates.Minority005.certificate106 := by decide +kernel
theorem exponentialBound106 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate318).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate212).dm (WitnessCertificates.Batch010.certificate212).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate212).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch026.certificate318).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch026.certificate319).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate212).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch026.certificate318 MergedCutGroups.Batch026.certificate319 CountingCertificates.Batch010.certificate212 CutLabelCertificates.Entropy005.certificate107 CutLabelCertificates.Minority005.certificate106 matches106 rfl rfl
    MergedCutGroups.Batch026.numericValid318 MergedCutGroups.Batch026.numericValid319 MergedCutGroups.Batch026.cellsSound318 MergedCutGroups.Batch026.cellsSound319
    MergedCutGroups.Batch026.cellsNumeric318 MergedCutGroups.Batch026.cellsNumeric319 MergedCutGroups.Batch026.populationMatches318 MergedCutGroups.Batch026.populationMatches319
    PopulationCertificates.Batch010.valid212 PopulationCertificates.Batch010.sound212 WitnessCertificates.Batch010.valid212 WitnessCertificates.Batch010.sound212 CountingCertificates.Batch010.valid212 CountingCertificates.Batch010.sound212
    CutLabelCertificates.Entropy005.valid107 CutLabelCertificates.Minority005.valid106 CutLabelCertificates.Minority005.sound106 H st hI
theorem probabilityBound106 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate318).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate212).dm (WitnessCertificates.Batch010.certificate212).beta) ≤ ((CutFailureCertificates.Budget010.certificate212).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound212 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate212).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate318).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate319).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate212).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate212).bound:ℝ) at hb
  exact (exponentialBound106 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches107 : (MergedCutGroups.Batch026.certificate321).GlobalMatches MergedCutGroups.Batch026.certificate322 CountingCertificates.Batch010.certificate214 CutLabelCertificates.Entropy005.certificate108 CutLabelCertificates.Minority005.certificate107 := by decide +kernel
theorem exponentialBound107 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate321).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate214).dm (WitnessCertificates.Batch010.certificate214).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate214).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch026.certificate321).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch026.certificate322).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate214).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch026.certificate321 MergedCutGroups.Batch026.certificate322 CountingCertificates.Batch010.certificate214 CutLabelCertificates.Entropy005.certificate108 CutLabelCertificates.Minority005.certificate107 matches107 rfl rfl
    MergedCutGroups.Batch026.numericValid321 MergedCutGroups.Batch026.numericValid322 MergedCutGroups.Batch026.cellsSound321 MergedCutGroups.Batch026.cellsSound322
    MergedCutGroups.Batch026.cellsNumeric321 MergedCutGroups.Batch026.cellsNumeric322 MergedCutGroups.Batch026.populationMatches321 MergedCutGroups.Batch026.populationMatches322
    PopulationCertificates.Batch010.valid214 PopulationCertificates.Batch010.sound214 WitnessCertificates.Batch010.valid214 WitnessCertificates.Batch010.sound214 CountingCertificates.Batch010.valid214 CountingCertificates.Batch010.sound214
    CutLabelCertificates.Entropy005.valid108 CutLabelCertificates.Minority005.valid107 CutLabelCertificates.Minority005.sound107 H st hI
theorem probabilityBound107 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch026.certificate321).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate214).dm (WitnessCertificates.Batch010.certificate214).beta) ≤ ((CutFailureCertificates.Budget010.certificate214).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound214 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate214).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate321).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch026.certificate322).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate214).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate214).bound:ℝ) at hb
  exact (exponentialBound107 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches108 : (MergedCutGroups.Batch027.certificate324).GlobalMatches MergedCutGroups.Batch027.certificate325 CountingCertificates.Batch010.certificate216 CutLabelCertificates.Entropy005.certificate109 CutLabelCertificates.Minority005.certificate108 := by decide +kernel
theorem exponentialBound108 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate324).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate216).dm (WitnessCertificates.Batch010.certificate216).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate216).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch027.certificate324).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch027.certificate325).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate216).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch027.certificate324 MergedCutGroups.Batch027.certificate325 CountingCertificates.Batch010.certificate216 CutLabelCertificates.Entropy005.certificate109 CutLabelCertificates.Minority005.certificate108 matches108 rfl rfl
    MergedCutGroups.Batch027.numericValid324 MergedCutGroups.Batch027.numericValid325 MergedCutGroups.Batch027.cellsSound324 MergedCutGroups.Batch027.cellsSound325
    MergedCutGroups.Batch027.cellsNumeric324 MergedCutGroups.Batch027.cellsNumeric325 MergedCutGroups.Batch027.populationMatches324 MergedCutGroups.Batch027.populationMatches325
    PopulationCertificates.Batch010.valid216 PopulationCertificates.Batch010.sound216 WitnessCertificates.Batch010.valid216 WitnessCertificates.Batch010.sound216 CountingCertificates.Batch010.valid216 CountingCertificates.Batch010.sound216
    CutLabelCertificates.Entropy005.valid109 CutLabelCertificates.Minority005.valid108 CutLabelCertificates.Minority005.sound108 H st hI
theorem probabilityBound108 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate324).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate216).dm (WitnessCertificates.Batch010.certificate216).beta) ≤ ((CutFailureCertificates.Budget010.certificate216).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound216 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate216).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate324).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate325).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate216).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate216).bound:ℝ) at hb
  exact (exponentialBound108 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches109 : (MergedCutGroups.Batch027.certificate327).GlobalMatches MergedCutGroups.Batch027.certificate328 CountingCertificates.Batch010.certificate218 CutLabelCertificates.Entropy005.certificate110 CutLabelCertificates.Minority005.certificate109 := by decide +kernel
theorem exponentialBound109 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate327).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate218).dm (WitnessCertificates.Batch010.certificate218).beta) ≤ (2*exp (-((CountingCertificates.Batch010.certificate218).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch027.certificate327).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch027.certificate328).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch010.certificate218).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch027.certificate327 MergedCutGroups.Batch027.certificate328 CountingCertificates.Batch010.certificate218 CutLabelCertificates.Entropy005.certificate110 CutLabelCertificates.Minority005.certificate109 matches109 rfl rfl
    MergedCutGroups.Batch027.numericValid327 MergedCutGroups.Batch027.numericValid328 MergedCutGroups.Batch027.cellsSound327 MergedCutGroups.Batch027.cellsSound328
    MergedCutGroups.Batch027.cellsNumeric327 MergedCutGroups.Batch027.cellsNumeric328 MergedCutGroups.Batch027.populationMatches327 MergedCutGroups.Batch027.populationMatches328
    PopulationCertificates.Batch010.valid218 PopulationCertificates.Batch010.sound218 WitnessCertificates.Batch010.valid218 WitnessCertificates.Batch010.sound218 CountingCertificates.Batch010.valid218 CountingCertificates.Batch010.sound218
    CutLabelCertificates.Entropy005.valid110 CutLabelCertificates.Minority005.valid109 CutLabelCertificates.Minority005.sound109 H st hI
theorem probabilityBound109 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate327).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch010.certificate218).dm (WitnessCertificates.Batch010.certificate218).beta) ≤ ((CutFailureCertificates.Budget010.certificate218).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget010.sound218 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch010.certificate218).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate327).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate328).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch010.certificate218).omega:ℝ) ≤ ((CutFailureCertificates.Budget010.certificate218).bound:ℝ) at hb
  exact (exponentialBound109 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches110 : (MergedCutGroups.Batch027.certificate330).GlobalMatches MergedCutGroups.Batch027.certificate331 CountingCertificates.Batch011.certificate220 CutLabelCertificates.Entropy005.certificate111 CutLabelCertificates.Minority005.certificate110 := by decide +kernel
theorem exponentialBound110 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate330).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate220).dm (WitnessCertificates.Batch011.certificate220).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate220).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch027.certificate330).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch027.certificate331).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate220).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch027.certificate330 MergedCutGroups.Batch027.certificate331 CountingCertificates.Batch011.certificate220 CutLabelCertificates.Entropy005.certificate111 CutLabelCertificates.Minority005.certificate110 matches110 rfl rfl
    MergedCutGroups.Batch027.numericValid330 MergedCutGroups.Batch027.numericValid331 MergedCutGroups.Batch027.cellsSound330 MergedCutGroups.Batch027.cellsSound331
    MergedCutGroups.Batch027.cellsNumeric330 MergedCutGroups.Batch027.cellsNumeric331 MergedCutGroups.Batch027.populationMatches330 MergedCutGroups.Batch027.populationMatches331
    PopulationCertificates.Batch011.valid220 PopulationCertificates.Batch011.sound220 WitnessCertificates.Batch011.valid220 WitnessCertificates.Batch011.sound220 CountingCertificates.Batch011.valid220 CountingCertificates.Batch011.sound220
    CutLabelCertificates.Entropy005.valid111 CutLabelCertificates.Minority005.valid110 CutLabelCertificates.Minority005.sound110 H st hI
theorem probabilityBound110 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate330).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate220).dm (WitnessCertificates.Batch011.certificate220).beta) ≤ ((CutFailureCertificates.Budget011.certificate220).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound220 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate220).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate330).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate331).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate220).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate220).bound:ℝ) at hb
  exact (exponentialBound110 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches111 : (MergedCutGroups.Batch027.certificate333).GlobalMatches MergedCutGroups.Batch027.certificate334 CountingCertificates.Batch011.certificate222 CutLabelCertificates.Entropy005.certificate112 CutLabelCertificates.Minority005.certificate111 := by decide +kernel
theorem exponentialBound111 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate333).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate222).dm (WitnessCertificates.Batch011.certificate222).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate222).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch027.certificate333).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch027.certificate334).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate222).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch027.certificate333 MergedCutGroups.Batch027.certificate334 CountingCertificates.Batch011.certificate222 CutLabelCertificates.Entropy005.certificate112 CutLabelCertificates.Minority005.certificate111 matches111 rfl rfl
    MergedCutGroups.Batch027.numericValid333 MergedCutGroups.Batch027.numericValid334 MergedCutGroups.Batch027.cellsSound333 MergedCutGroups.Batch027.cellsSound334
    MergedCutGroups.Batch027.cellsNumeric333 MergedCutGroups.Batch027.cellsNumeric334 MergedCutGroups.Batch027.populationMatches333 MergedCutGroups.Batch027.populationMatches334
    PopulationCertificates.Batch011.valid222 PopulationCertificates.Batch011.sound222 WitnessCertificates.Batch011.valid222 WitnessCertificates.Batch011.sound222 CountingCertificates.Batch011.valid222 CountingCertificates.Batch011.sound222
    CutLabelCertificates.Entropy005.valid112 CutLabelCertificates.Minority005.valid111 CutLabelCertificates.Minority005.sound111 H st hI
theorem probabilityBound111 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch027.certificate333).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate222).dm (WitnessCertificates.Batch011.certificate222).beta) ≤ ((CutFailureCertificates.Budget011.certificate222).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound222 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate222).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate333).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch027.certificate334).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate222).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate222).bound:ℝ) at hb
  exact (exponentialBound111 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches112 : (MergedCutGroups.Batch028.certificate336).GlobalMatches MergedCutGroups.Batch028.certificate337 CountingCertificates.Batch011.certificate224 CutLabelCertificates.Entropy005.certificate113 CutLabelCertificates.Minority005.certificate112 := by decide +kernel
theorem exponentialBound112 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate336).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate224).dm (WitnessCertificates.Batch011.certificate224).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate224).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch028.certificate336).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch028.certificate337).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate224).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch028.certificate336 MergedCutGroups.Batch028.certificate337 CountingCertificates.Batch011.certificate224 CutLabelCertificates.Entropy005.certificate113 CutLabelCertificates.Minority005.certificate112 matches112 rfl rfl
    MergedCutGroups.Batch028.numericValid336 MergedCutGroups.Batch028.numericValid337 MergedCutGroups.Batch028.cellsSound336 MergedCutGroups.Batch028.cellsSound337
    MergedCutGroups.Batch028.cellsNumeric336 MergedCutGroups.Batch028.cellsNumeric337 MergedCutGroups.Batch028.populationMatches336 MergedCutGroups.Batch028.populationMatches337
    PopulationCertificates.Batch011.valid224 PopulationCertificates.Batch011.sound224 WitnessCertificates.Batch011.valid224 WitnessCertificates.Batch011.sound224 CountingCertificates.Batch011.valid224 CountingCertificates.Batch011.sound224
    CutLabelCertificates.Entropy005.valid113 CutLabelCertificates.Minority005.valid112 CutLabelCertificates.Minority005.sound112 H st hI
theorem probabilityBound112 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate336).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate224).dm (WitnessCertificates.Batch011.certificate224).beta) ≤ ((CutFailureCertificates.Budget011.certificate224).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound224 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate224).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate336).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate337).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate224).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate224).bound:ℝ) at hb
  exact (exponentialBound112 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches113 : (MergedCutGroups.Batch028.certificate339).GlobalMatches MergedCutGroups.Batch028.certificate340 CountingCertificates.Batch011.certificate226 CutLabelCertificates.Entropy005.certificate114 CutLabelCertificates.Minority005.certificate113 := by decide +kernel
theorem exponentialBound113 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate339).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate226).dm (WitnessCertificates.Batch011.certificate226).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate226).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch028.certificate339).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch028.certificate340).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate226).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch028.certificate339 MergedCutGroups.Batch028.certificate340 CountingCertificates.Batch011.certificate226 CutLabelCertificates.Entropy005.certificate114 CutLabelCertificates.Minority005.certificate113 matches113 rfl rfl
    MergedCutGroups.Batch028.numericValid339 MergedCutGroups.Batch028.numericValid340 MergedCutGroups.Batch028.cellsSound339 MergedCutGroups.Batch028.cellsSound340
    MergedCutGroups.Batch028.cellsNumeric339 MergedCutGroups.Batch028.cellsNumeric340 MergedCutGroups.Batch028.populationMatches339 MergedCutGroups.Batch028.populationMatches340
    PopulationCertificates.Batch011.valid226 PopulationCertificates.Batch011.sound226 WitnessCertificates.Batch011.valid226 WitnessCertificates.Batch011.sound226 CountingCertificates.Batch011.valid226 CountingCertificates.Batch011.sound226
    CutLabelCertificates.Entropy005.valid114 CutLabelCertificates.Minority005.valid113 CutLabelCertificates.Minority005.sound113 H st hI
theorem probabilityBound113 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate339).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate226).dm (WitnessCertificates.Batch011.certificate226).beta) ≤ ((CutFailureCertificates.Budget011.certificate226).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound226 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate226).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate339).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate340).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate226).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate226).bound:ℝ) at hb
  exact (exponentialBound113 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches114 : (MergedCutGroups.Batch028.certificate342).GlobalMatches MergedCutGroups.Batch028.certificate343 CountingCertificates.Batch011.certificate228 CutLabelCertificates.Entropy005.certificate115 CutLabelCertificates.Minority005.certificate114 := by decide +kernel
theorem exponentialBound114 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate342).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate228).dm (WitnessCertificates.Batch011.certificate228).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate228).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch028.certificate342).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch028.certificate343).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate228).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch028.certificate342 MergedCutGroups.Batch028.certificate343 CountingCertificates.Batch011.certificate228 CutLabelCertificates.Entropy005.certificate115 CutLabelCertificates.Minority005.certificate114 matches114 rfl rfl
    MergedCutGroups.Batch028.numericValid342 MergedCutGroups.Batch028.numericValid343 MergedCutGroups.Batch028.cellsSound342 MergedCutGroups.Batch028.cellsSound343
    MergedCutGroups.Batch028.cellsNumeric342 MergedCutGroups.Batch028.cellsNumeric343 MergedCutGroups.Batch028.populationMatches342 MergedCutGroups.Batch028.populationMatches343
    PopulationCertificates.Batch011.valid228 PopulationCertificates.Batch011.sound228 WitnessCertificates.Batch011.valid228 WitnessCertificates.Batch011.sound228 CountingCertificates.Batch011.valid228 CountingCertificates.Batch011.sound228
    CutLabelCertificates.Entropy005.valid115 CutLabelCertificates.Minority005.valid114 CutLabelCertificates.Minority005.sound114 H st hI
theorem probabilityBound114 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate342).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate228).dm (WitnessCertificates.Batch011.certificate228).beta) ≤ ((CutFailureCertificates.Budget011.certificate228).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound228 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate228).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate342).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate343).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate228).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate228).bound:ℝ) at hb
  exact (exponentialBound114 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches115 : (MergedCutGroups.Batch028.certificate345).GlobalMatches MergedCutGroups.Batch028.certificate346 CountingCertificates.Batch011.certificate230 CutLabelCertificates.Entropy005.certificate116 CutLabelCertificates.Minority005.certificate115 := by decide +kernel
theorem exponentialBound115 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate345).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate230).dm (WitnessCertificates.Batch011.certificate230).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate230).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch028.certificate345).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch028.certificate346).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate230).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch028.certificate345 MergedCutGroups.Batch028.certificate346 CountingCertificates.Batch011.certificate230 CutLabelCertificates.Entropy005.certificate116 CutLabelCertificates.Minority005.certificate115 matches115 rfl rfl
    MergedCutGroups.Batch028.numericValid345 MergedCutGroups.Batch028.numericValid346 MergedCutGroups.Batch028.cellsSound345 MergedCutGroups.Batch028.cellsSound346
    MergedCutGroups.Batch028.cellsNumeric345 MergedCutGroups.Batch028.cellsNumeric346 MergedCutGroups.Batch028.populationMatches345 MergedCutGroups.Batch028.populationMatches346
    PopulationCertificates.Batch011.valid230 PopulationCertificates.Batch011.sound230 WitnessCertificates.Batch011.valid230 WitnessCertificates.Batch011.sound230 CountingCertificates.Batch011.valid230 CountingCertificates.Batch011.sound230
    CutLabelCertificates.Entropy005.valid116 CutLabelCertificates.Minority005.valid115 CutLabelCertificates.Minority005.sound115 H st hI
theorem probabilityBound115 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch028.certificate345).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate230).dm (WitnessCertificates.Batch011.certificate230).beta) ≤ ((CutFailureCertificates.Budget011.certificate230).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound230 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate230).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate345).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch028.certificate346).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate230).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate230).bound:ℝ) at hb
  exact (exponentialBound115 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches116 : (MergedCutGroups.Batch029.certificate348).GlobalMatches MergedCutGroups.Batch029.certificate349 CountingCertificates.Batch011.certificate232 CutLabelCertificates.Entropy005.certificate117 CutLabelCertificates.Minority005.certificate116 := by decide +kernel
theorem exponentialBound116 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate348).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate232).dm (WitnessCertificates.Batch011.certificate232).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate232).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch029.certificate348).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch029.certificate349).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate232).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch029.certificate348 MergedCutGroups.Batch029.certificate349 CountingCertificates.Batch011.certificate232 CutLabelCertificates.Entropy005.certificate117 CutLabelCertificates.Minority005.certificate116 matches116 rfl rfl
    MergedCutGroups.Batch029.numericValid348 MergedCutGroups.Batch029.numericValid349 MergedCutGroups.Batch029.cellsSound348 MergedCutGroups.Batch029.cellsSound349
    MergedCutGroups.Batch029.cellsNumeric348 MergedCutGroups.Batch029.cellsNumeric349 MergedCutGroups.Batch029.populationMatches348 MergedCutGroups.Batch029.populationMatches349
    PopulationCertificates.Batch011.valid232 PopulationCertificates.Batch011.sound232 WitnessCertificates.Batch011.valid232 WitnessCertificates.Batch011.sound232 CountingCertificates.Batch011.valid232 CountingCertificates.Batch011.sound232
    CutLabelCertificates.Entropy005.valid117 CutLabelCertificates.Minority005.valid116 CutLabelCertificates.Minority005.sound116 H st hI
theorem probabilityBound116 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate348).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate232).dm (WitnessCertificates.Batch011.certificate232).beta) ≤ ((CutFailureCertificates.Budget011.certificate232).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound232 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate232).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate348).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate349).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate232).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate232).bound:ℝ) at hb
  exact (exponentialBound116 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches117 : (MergedCutGroups.Batch029.certificate351).GlobalMatches MergedCutGroups.Batch029.certificate352 CountingCertificates.Batch011.certificate234 CutLabelCertificates.Entropy005.certificate118 CutLabelCertificates.Minority005.certificate117 := by decide +kernel
theorem exponentialBound117 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate351).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate234).dm (WitnessCertificates.Batch011.certificate234).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate234).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch029.certificate351).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch029.certificate352).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate234).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch029.certificate351 MergedCutGroups.Batch029.certificate352 CountingCertificates.Batch011.certificate234 CutLabelCertificates.Entropy005.certificate118 CutLabelCertificates.Minority005.certificate117 matches117 rfl rfl
    MergedCutGroups.Batch029.numericValid351 MergedCutGroups.Batch029.numericValid352 MergedCutGroups.Batch029.cellsSound351 MergedCutGroups.Batch029.cellsSound352
    MergedCutGroups.Batch029.cellsNumeric351 MergedCutGroups.Batch029.cellsNumeric352 MergedCutGroups.Batch029.populationMatches351 MergedCutGroups.Batch029.populationMatches352
    PopulationCertificates.Batch011.valid234 PopulationCertificates.Batch011.sound234 WitnessCertificates.Batch011.valid234 WitnessCertificates.Batch011.sound234 CountingCertificates.Batch011.valid234 CountingCertificates.Batch011.sound234
    CutLabelCertificates.Entropy005.valid118 CutLabelCertificates.Minority005.valid117 CutLabelCertificates.Minority005.sound117 H st hI
theorem probabilityBound117 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate351).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate234).dm (WitnessCertificates.Batch011.certificate234).beta) ≤ ((CutFailureCertificates.Budget011.certificate234).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound234 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate234).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate351).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate352).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate234).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate234).bound:ℝ) at hb
  exact (exponentialBound117 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches118 : (MergedCutGroups.Batch029.certificate354).GlobalMatches MergedCutGroups.Batch029.certificate355 CountingCertificates.Batch011.certificate236 CutLabelCertificates.Entropy005.certificate119 CutLabelCertificates.Minority005.certificate118 := by decide +kernel
theorem exponentialBound118 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate354).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate236).dm (WitnessCertificates.Batch011.certificate236).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate236).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch029.certificate354).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch029.certificate355).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate236).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch029.certificate354 MergedCutGroups.Batch029.certificate355 CountingCertificates.Batch011.certificate236 CutLabelCertificates.Entropy005.certificate119 CutLabelCertificates.Minority005.certificate118 matches118 rfl rfl
    MergedCutGroups.Batch029.numericValid354 MergedCutGroups.Batch029.numericValid355 MergedCutGroups.Batch029.cellsSound354 MergedCutGroups.Batch029.cellsSound355
    MergedCutGroups.Batch029.cellsNumeric354 MergedCutGroups.Batch029.cellsNumeric355 MergedCutGroups.Batch029.populationMatches354 MergedCutGroups.Batch029.populationMatches355
    PopulationCertificates.Batch011.valid236 PopulationCertificates.Batch011.sound236 WitnessCertificates.Batch011.valid236 WitnessCertificates.Batch011.sound236 CountingCertificates.Batch011.valid236 CountingCertificates.Batch011.sound236
    CutLabelCertificates.Entropy005.valid119 CutLabelCertificates.Minority005.valid118 CutLabelCertificates.Minority005.sound118 H st hI
theorem probabilityBound118 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate354).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate236).dm (WitnessCertificates.Batch011.certificate236).beta) ≤ ((CutFailureCertificates.Budget011.certificate236).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound236 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate236).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate354).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate355).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate236).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate236).bound:ℝ) at hb
  exact (exponentialBound118 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches119 : (MergedCutGroups.Batch029.certificate357).GlobalMatches MergedCutGroups.Batch029.certificate358 CountingCertificates.Batch011.certificate238 CutLabelCertificates.Entropy006.certificate120 CutLabelCertificates.Minority005.certificate119 := by decide +kernel
theorem exponentialBound119 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate357).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate238).dm (WitnessCertificates.Batch011.certificate238).beta) ≤ (2*exp (-((CountingCertificates.Batch011.certificate238).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch029.certificate357).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch029.certificate358).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch011.certificate238).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch029.certificate357 MergedCutGroups.Batch029.certificate358 CountingCertificates.Batch011.certificate238 CutLabelCertificates.Entropy006.certificate120 CutLabelCertificates.Minority005.certificate119 matches119 rfl rfl
    MergedCutGroups.Batch029.numericValid357 MergedCutGroups.Batch029.numericValid358 MergedCutGroups.Batch029.cellsSound357 MergedCutGroups.Batch029.cellsSound358
    MergedCutGroups.Batch029.cellsNumeric357 MergedCutGroups.Batch029.cellsNumeric358 MergedCutGroups.Batch029.populationMatches357 MergedCutGroups.Batch029.populationMatches358
    PopulationCertificates.Batch011.valid238 PopulationCertificates.Batch011.sound238 WitnessCertificates.Batch011.valid238 WitnessCertificates.Batch011.sound238 CountingCertificates.Batch011.valid238 CountingCertificates.Batch011.sound238
    CutLabelCertificates.Entropy006.valid120 CutLabelCertificates.Minority005.valid119 CutLabelCertificates.Minority005.sound119 H st hI
theorem probabilityBound119 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch029.certificate357).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch011.certificate238).dm (WitnessCertificates.Batch011.certificate238).beta) ≤ ((CutFailureCertificates.Budget011.certificate238).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget011.sound238 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch011.certificate238).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate357).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch029.certificate358).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch011.certificate238).omega:ℝ) ≤ ((CutFailureCertificates.Budget011.certificate238).bound:ℝ) at hb
  exact (exponentialBound119 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch005
