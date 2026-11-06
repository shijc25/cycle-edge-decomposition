import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch004
import Cycle12.CountingCertificates.Batch005
import Cycle12.CutFailureCertificates.Budget004
import Cycle12.CutFailureCertificates.Budget005
import Cycle12.CutLabelCertificates.Entropy002
import Cycle12.CutLabelCertificates.Entropy003
import Cycle12.CutLabelCertificates.Minority002
import Cycle12.MergedCutGroups.Batch010
import Cycle12.MergedCutGroups.Batch011
import Cycle12.MergedCutGroups.Batch012
import Cycle12.MergedCutGroups.Batch013
import Cycle12.MergedCutGroups.Batch014
import Cycle12.PopulationCertificates.Batch004
import Cycle12.PopulationCertificates.Batch005
import Cycle12.WitnessCertificates.Batch004
import Cycle12.WitnessCertificates.Batch005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch002
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches40 : (MergedCutGroups.Batch010.certificate120).GlobalMatches MergedCutGroups.Batch010.certificate121 CountingCertificates.Batch004.certificate80 CutLabelCertificates.Entropy002.certificate41 CutLabelCertificates.Minority002.certificate40 := by decide +kernel
theorem exponentialBound40 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate120).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate80).dm (WitnessCertificates.Batch004.certificate80).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate80).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch010.certificate120).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch010.certificate121).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate80).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch010.certificate120 MergedCutGroups.Batch010.certificate121 CountingCertificates.Batch004.certificate80 CutLabelCertificates.Entropy002.certificate41 CutLabelCertificates.Minority002.certificate40 matches40 rfl rfl
    MergedCutGroups.Batch010.numericValid120 MergedCutGroups.Batch010.numericValid121 MergedCutGroups.Batch010.cellsSound120 MergedCutGroups.Batch010.cellsSound121
    MergedCutGroups.Batch010.cellsNumeric120 MergedCutGroups.Batch010.cellsNumeric121 MergedCutGroups.Batch010.populationMatches120 MergedCutGroups.Batch010.populationMatches121
    PopulationCertificates.Batch004.valid80 PopulationCertificates.Batch004.sound80 WitnessCertificates.Batch004.valid80 WitnessCertificates.Batch004.sound80 CountingCertificates.Batch004.valid80 CountingCertificates.Batch004.sound80
    CutLabelCertificates.Entropy002.valid41 CutLabelCertificates.Minority002.valid40 CutLabelCertificates.Minority002.sound40 H st hI
theorem probabilityBound40 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate120).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate80).dm (WitnessCertificates.Batch004.certificate80).beta) ≤ ((CutFailureCertificates.Budget004.certificate80).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound80 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate80).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate120).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate121).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate80).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate80).bound:ℝ) at hb
  exact (exponentialBound40 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches41 : (MergedCutGroups.Batch010.certificate123).GlobalMatches MergedCutGroups.Batch010.certificate124 CountingCertificates.Batch004.certificate82 CutLabelCertificates.Entropy002.certificate42 CutLabelCertificates.Minority002.certificate41 := by decide +kernel
theorem exponentialBound41 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate123).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate82).dm (WitnessCertificates.Batch004.certificate82).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate82).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch010.certificate123).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch010.certificate124).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate82).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch010.certificate123 MergedCutGroups.Batch010.certificate124 CountingCertificates.Batch004.certificate82 CutLabelCertificates.Entropy002.certificate42 CutLabelCertificates.Minority002.certificate41 matches41 rfl rfl
    MergedCutGroups.Batch010.numericValid123 MergedCutGroups.Batch010.numericValid124 MergedCutGroups.Batch010.cellsSound123 MergedCutGroups.Batch010.cellsSound124
    MergedCutGroups.Batch010.cellsNumeric123 MergedCutGroups.Batch010.cellsNumeric124 MergedCutGroups.Batch010.populationMatches123 MergedCutGroups.Batch010.populationMatches124
    PopulationCertificates.Batch004.valid82 PopulationCertificates.Batch004.sound82 WitnessCertificates.Batch004.valid82 WitnessCertificates.Batch004.sound82 CountingCertificates.Batch004.valid82 CountingCertificates.Batch004.sound82
    CutLabelCertificates.Entropy002.valid42 CutLabelCertificates.Minority002.valid41 CutLabelCertificates.Minority002.sound41 H st hI
theorem probabilityBound41 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate123).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate82).dm (WitnessCertificates.Batch004.certificate82).beta) ≤ ((CutFailureCertificates.Budget004.certificate82).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound82 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate82).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate123).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate124).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate82).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate82).bound:ℝ) at hb
  exact (exponentialBound41 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches42 : (MergedCutGroups.Batch010.certificate126).GlobalMatches MergedCutGroups.Batch010.certificate127 CountingCertificates.Batch004.certificate84 CutLabelCertificates.Entropy002.certificate43 CutLabelCertificates.Minority002.certificate42 := by decide +kernel
theorem exponentialBound42 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate126).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate84).dm (WitnessCertificates.Batch004.certificate84).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate84).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch010.certificate126).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch010.certificate127).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate84).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch010.certificate126 MergedCutGroups.Batch010.certificate127 CountingCertificates.Batch004.certificate84 CutLabelCertificates.Entropy002.certificate43 CutLabelCertificates.Minority002.certificate42 matches42 rfl rfl
    MergedCutGroups.Batch010.numericValid126 MergedCutGroups.Batch010.numericValid127 MergedCutGroups.Batch010.cellsSound126 MergedCutGroups.Batch010.cellsSound127
    MergedCutGroups.Batch010.cellsNumeric126 MergedCutGroups.Batch010.cellsNumeric127 MergedCutGroups.Batch010.populationMatches126 MergedCutGroups.Batch010.populationMatches127
    PopulationCertificates.Batch004.valid84 PopulationCertificates.Batch004.sound84 WitnessCertificates.Batch004.valid84 WitnessCertificates.Batch004.sound84 CountingCertificates.Batch004.valid84 CountingCertificates.Batch004.sound84
    CutLabelCertificates.Entropy002.valid43 CutLabelCertificates.Minority002.valid42 CutLabelCertificates.Minority002.sound42 H st hI
theorem probabilityBound42 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate126).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate84).dm (WitnessCertificates.Batch004.certificate84).beta) ≤ ((CutFailureCertificates.Budget004.certificate84).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound84 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate84).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate126).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate127).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate84).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate84).bound:ℝ) at hb
  exact (exponentialBound42 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches43 : (MergedCutGroups.Batch010.certificate129).GlobalMatches MergedCutGroups.Batch010.certificate130 CountingCertificates.Batch004.certificate86 CutLabelCertificates.Entropy002.certificate44 CutLabelCertificates.Minority002.certificate43 := by decide +kernel
theorem exponentialBound43 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate129).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate86).dm (WitnessCertificates.Batch004.certificate86).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate86).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch010.certificate129).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch010.certificate130).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate86).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch010.certificate129 MergedCutGroups.Batch010.certificate130 CountingCertificates.Batch004.certificate86 CutLabelCertificates.Entropy002.certificate44 CutLabelCertificates.Minority002.certificate43 matches43 rfl rfl
    MergedCutGroups.Batch010.numericValid129 MergedCutGroups.Batch010.numericValid130 MergedCutGroups.Batch010.cellsSound129 MergedCutGroups.Batch010.cellsSound130
    MergedCutGroups.Batch010.cellsNumeric129 MergedCutGroups.Batch010.cellsNumeric130 MergedCutGroups.Batch010.populationMatches129 MergedCutGroups.Batch010.populationMatches130
    PopulationCertificates.Batch004.valid86 PopulationCertificates.Batch004.sound86 WitnessCertificates.Batch004.valid86 WitnessCertificates.Batch004.sound86 CountingCertificates.Batch004.valid86 CountingCertificates.Batch004.sound86
    CutLabelCertificates.Entropy002.valid44 CutLabelCertificates.Minority002.valid43 CutLabelCertificates.Minority002.sound43 H st hI
theorem probabilityBound43 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate129).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate86).dm (WitnessCertificates.Batch004.certificate86).beta) ≤ ((CutFailureCertificates.Budget004.certificate86).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound86 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate86).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate129).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate130).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate86).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate86).bound:ℝ) at hb
  exact (exponentialBound43 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches44 : (MergedCutGroups.Batch011.certificate132).GlobalMatches MergedCutGroups.Batch011.certificate133 CountingCertificates.Batch004.certificate88 CutLabelCertificates.Entropy002.certificate45 CutLabelCertificates.Minority002.certificate44 := by decide +kernel
theorem exponentialBound44 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate132).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate88).dm (WitnessCertificates.Batch004.certificate88).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate88).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch011.certificate132).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch011.certificate133).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate88).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch011.certificate132 MergedCutGroups.Batch011.certificate133 CountingCertificates.Batch004.certificate88 CutLabelCertificates.Entropy002.certificate45 CutLabelCertificates.Minority002.certificate44 matches44 rfl rfl
    MergedCutGroups.Batch011.numericValid132 MergedCutGroups.Batch011.numericValid133 MergedCutGroups.Batch011.cellsSound132 MergedCutGroups.Batch011.cellsSound133
    MergedCutGroups.Batch011.cellsNumeric132 MergedCutGroups.Batch011.cellsNumeric133 MergedCutGroups.Batch011.populationMatches132 MergedCutGroups.Batch011.populationMatches133
    PopulationCertificates.Batch004.valid88 PopulationCertificates.Batch004.sound88 WitnessCertificates.Batch004.valid88 WitnessCertificates.Batch004.sound88 CountingCertificates.Batch004.valid88 CountingCertificates.Batch004.sound88
    CutLabelCertificates.Entropy002.valid45 CutLabelCertificates.Minority002.valid44 CutLabelCertificates.Minority002.sound44 H st hI
theorem probabilityBound44 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate132).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate88).dm (WitnessCertificates.Batch004.certificate88).beta) ≤ ((CutFailureCertificates.Budget004.certificate88).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound88 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate88).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate132).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate133).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate88).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate88).bound:ℝ) at hb
  exact (exponentialBound44 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches45 : (MergedCutGroups.Batch011.certificate135).GlobalMatches MergedCutGroups.Batch011.certificate136 CountingCertificates.Batch004.certificate90 CutLabelCertificates.Entropy002.certificate46 CutLabelCertificates.Minority002.certificate45 := by decide +kernel
theorem exponentialBound45 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate135).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate90).dm (WitnessCertificates.Batch004.certificate90).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate90).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch011.certificate135).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch011.certificate136).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate90).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch011.certificate135 MergedCutGroups.Batch011.certificate136 CountingCertificates.Batch004.certificate90 CutLabelCertificates.Entropy002.certificate46 CutLabelCertificates.Minority002.certificate45 matches45 rfl rfl
    MergedCutGroups.Batch011.numericValid135 MergedCutGroups.Batch011.numericValid136 MergedCutGroups.Batch011.cellsSound135 MergedCutGroups.Batch011.cellsSound136
    MergedCutGroups.Batch011.cellsNumeric135 MergedCutGroups.Batch011.cellsNumeric136 MergedCutGroups.Batch011.populationMatches135 MergedCutGroups.Batch011.populationMatches136
    PopulationCertificates.Batch004.valid90 PopulationCertificates.Batch004.sound90 WitnessCertificates.Batch004.valid90 WitnessCertificates.Batch004.sound90 CountingCertificates.Batch004.valid90 CountingCertificates.Batch004.sound90
    CutLabelCertificates.Entropy002.valid46 CutLabelCertificates.Minority002.valid45 CutLabelCertificates.Minority002.sound45 H st hI
theorem probabilityBound45 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate135).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate90).dm (WitnessCertificates.Batch004.certificate90).beta) ≤ ((CutFailureCertificates.Budget004.certificate90).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound90 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate90).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate135).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate136).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate90).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate90).bound:ℝ) at hb
  exact (exponentialBound45 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches46 : (MergedCutGroups.Batch011.certificate138).GlobalMatches MergedCutGroups.Batch011.certificate139 CountingCertificates.Batch004.certificate92 CutLabelCertificates.Entropy002.certificate47 CutLabelCertificates.Minority002.certificate46 := by decide +kernel
theorem exponentialBound46 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate138).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate92).dm (WitnessCertificates.Batch004.certificate92).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate92).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch011.certificate138).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch011.certificate139).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate92).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch011.certificate138 MergedCutGroups.Batch011.certificate139 CountingCertificates.Batch004.certificate92 CutLabelCertificates.Entropy002.certificate47 CutLabelCertificates.Minority002.certificate46 matches46 rfl rfl
    MergedCutGroups.Batch011.numericValid138 MergedCutGroups.Batch011.numericValid139 MergedCutGroups.Batch011.cellsSound138 MergedCutGroups.Batch011.cellsSound139
    MergedCutGroups.Batch011.cellsNumeric138 MergedCutGroups.Batch011.cellsNumeric139 MergedCutGroups.Batch011.populationMatches138 MergedCutGroups.Batch011.populationMatches139
    PopulationCertificates.Batch004.valid92 PopulationCertificates.Batch004.sound92 WitnessCertificates.Batch004.valid92 WitnessCertificates.Batch004.sound92 CountingCertificates.Batch004.valid92 CountingCertificates.Batch004.sound92
    CutLabelCertificates.Entropy002.valid47 CutLabelCertificates.Minority002.valid46 CutLabelCertificates.Minority002.sound46 H st hI
theorem probabilityBound46 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate138).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate92).dm (WitnessCertificates.Batch004.certificate92).beta) ≤ ((CutFailureCertificates.Budget004.certificate92).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound92 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate92).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate138).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate139).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate92).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate92).bound:ℝ) at hb
  exact (exponentialBound46 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches47 : (MergedCutGroups.Batch011.certificate141).GlobalMatches MergedCutGroups.Batch011.certificate142 CountingCertificates.Batch004.certificate94 CutLabelCertificates.Entropy002.certificate48 CutLabelCertificates.Minority002.certificate47 := by decide +kernel
theorem exponentialBound47 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate141).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate94).dm (WitnessCertificates.Batch004.certificate94).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate94).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch011.certificate141).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch011.certificate142).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate94).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch011.certificate141 MergedCutGroups.Batch011.certificate142 CountingCertificates.Batch004.certificate94 CutLabelCertificates.Entropy002.certificate48 CutLabelCertificates.Minority002.certificate47 matches47 rfl rfl
    MergedCutGroups.Batch011.numericValid141 MergedCutGroups.Batch011.numericValid142 MergedCutGroups.Batch011.cellsSound141 MergedCutGroups.Batch011.cellsSound142
    MergedCutGroups.Batch011.cellsNumeric141 MergedCutGroups.Batch011.cellsNumeric142 MergedCutGroups.Batch011.populationMatches141 MergedCutGroups.Batch011.populationMatches142
    PopulationCertificates.Batch004.valid94 PopulationCertificates.Batch004.sound94 WitnessCertificates.Batch004.valid94 WitnessCertificates.Batch004.sound94 CountingCertificates.Batch004.valid94 CountingCertificates.Batch004.sound94
    CutLabelCertificates.Entropy002.valid48 CutLabelCertificates.Minority002.valid47 CutLabelCertificates.Minority002.sound47 H st hI
theorem probabilityBound47 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate141).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate94).dm (WitnessCertificates.Batch004.certificate94).beta) ≤ ((CutFailureCertificates.Budget004.certificate94).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound94 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate94).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate141).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate142).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate94).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate94).bound:ℝ) at hb
  exact (exponentialBound47 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches48 : (MergedCutGroups.Batch012.certificate144).GlobalMatches MergedCutGroups.Batch012.certificate145 CountingCertificates.Batch004.certificate96 CutLabelCertificates.Entropy002.certificate49 CutLabelCertificates.Minority002.certificate48 := by decide +kernel
theorem exponentialBound48 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate144).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate96).dm (WitnessCertificates.Batch004.certificate96).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate96).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch012.certificate144).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch012.certificate145).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate96).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch012.certificate144 MergedCutGroups.Batch012.certificate145 CountingCertificates.Batch004.certificate96 CutLabelCertificates.Entropy002.certificate49 CutLabelCertificates.Minority002.certificate48 matches48 rfl rfl
    MergedCutGroups.Batch012.numericValid144 MergedCutGroups.Batch012.numericValid145 MergedCutGroups.Batch012.cellsSound144 MergedCutGroups.Batch012.cellsSound145
    MergedCutGroups.Batch012.cellsNumeric144 MergedCutGroups.Batch012.cellsNumeric145 MergedCutGroups.Batch012.populationMatches144 MergedCutGroups.Batch012.populationMatches145
    PopulationCertificates.Batch004.valid96 PopulationCertificates.Batch004.sound96 WitnessCertificates.Batch004.valid96 WitnessCertificates.Batch004.sound96 CountingCertificates.Batch004.valid96 CountingCertificates.Batch004.sound96
    CutLabelCertificates.Entropy002.valid49 CutLabelCertificates.Minority002.valid48 CutLabelCertificates.Minority002.sound48 H st hI
theorem probabilityBound48 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate144).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate96).dm (WitnessCertificates.Batch004.certificate96).beta) ≤ ((CutFailureCertificates.Budget004.certificate96).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound96 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate96).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate144).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate145).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate96).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate96).bound:ℝ) at hb
  exact (exponentialBound48 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches49 : (MergedCutGroups.Batch012.certificate147).GlobalMatches MergedCutGroups.Batch012.certificate148 CountingCertificates.Batch004.certificate98 CutLabelCertificates.Entropy002.certificate50 CutLabelCertificates.Minority002.certificate49 := by decide +kernel
theorem exponentialBound49 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate147).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate98).dm (WitnessCertificates.Batch004.certificate98).beta) ≤ (2*exp (-((CountingCertificates.Batch004.certificate98).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch012.certificate147).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch012.certificate148).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch004.certificate98).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch012.certificate147 MergedCutGroups.Batch012.certificate148 CountingCertificates.Batch004.certificate98 CutLabelCertificates.Entropy002.certificate50 CutLabelCertificates.Minority002.certificate49 matches49 rfl rfl
    MergedCutGroups.Batch012.numericValid147 MergedCutGroups.Batch012.numericValid148 MergedCutGroups.Batch012.cellsSound147 MergedCutGroups.Batch012.cellsSound148
    MergedCutGroups.Batch012.cellsNumeric147 MergedCutGroups.Batch012.cellsNumeric148 MergedCutGroups.Batch012.populationMatches147 MergedCutGroups.Batch012.populationMatches148
    PopulationCertificates.Batch004.valid98 PopulationCertificates.Batch004.sound98 WitnessCertificates.Batch004.valid98 WitnessCertificates.Batch004.sound98 CountingCertificates.Batch004.valid98 CountingCertificates.Batch004.sound98
    CutLabelCertificates.Entropy002.valid50 CutLabelCertificates.Minority002.valid49 CutLabelCertificates.Minority002.sound49 H st hI
theorem probabilityBound49 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate147).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch004.certificate98).dm (WitnessCertificates.Batch004.certificate98).beta) ≤ ((CutFailureCertificates.Budget004.certificate98).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound98 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate98).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate147).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate148).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch004.certificate98).omega:ℝ) ≤ ((CutFailureCertificates.Budget004.certificate98).bound:ℝ) at hb
  exact (exponentialBound49 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches50 : (MergedCutGroups.Batch012.certificate150).GlobalMatches MergedCutGroups.Batch012.certificate151 CountingCertificates.Batch005.certificate100 CutLabelCertificates.Entropy002.certificate51 CutLabelCertificates.Minority002.certificate50 := by decide +kernel
theorem exponentialBound50 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate150).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate100).dm (WitnessCertificates.Batch005.certificate100).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate100).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch012.certificate150).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch012.certificate151).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate100).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch012.certificate150 MergedCutGroups.Batch012.certificate151 CountingCertificates.Batch005.certificate100 CutLabelCertificates.Entropy002.certificate51 CutLabelCertificates.Minority002.certificate50 matches50 rfl rfl
    MergedCutGroups.Batch012.numericValid150 MergedCutGroups.Batch012.numericValid151 MergedCutGroups.Batch012.cellsSound150 MergedCutGroups.Batch012.cellsSound151
    MergedCutGroups.Batch012.cellsNumeric150 MergedCutGroups.Batch012.cellsNumeric151 MergedCutGroups.Batch012.populationMatches150 MergedCutGroups.Batch012.populationMatches151
    PopulationCertificates.Batch005.valid100 PopulationCertificates.Batch005.sound100 WitnessCertificates.Batch005.valid100 WitnessCertificates.Batch005.sound100 CountingCertificates.Batch005.valid100 CountingCertificates.Batch005.sound100
    CutLabelCertificates.Entropy002.valid51 CutLabelCertificates.Minority002.valid50 CutLabelCertificates.Minority002.sound50 H st hI
theorem probabilityBound50 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate150).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate100).dm (WitnessCertificates.Batch005.certificate100).beta) ≤ ((CutFailureCertificates.Budget005.certificate100).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound100 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate100).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate150).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate151).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate100).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate100).bound:ℝ) at hb
  exact (exponentialBound50 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches51 : (MergedCutGroups.Batch012.certificate153).GlobalMatches MergedCutGroups.Batch012.certificate154 CountingCertificates.Batch005.certificate102 CutLabelCertificates.Entropy002.certificate52 CutLabelCertificates.Minority002.certificate51 := by decide +kernel
theorem exponentialBound51 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate153).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate102).dm (WitnessCertificates.Batch005.certificate102).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate102).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch012.certificate153).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch012.certificate154).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate102).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch012.certificate153 MergedCutGroups.Batch012.certificate154 CountingCertificates.Batch005.certificate102 CutLabelCertificates.Entropy002.certificate52 CutLabelCertificates.Minority002.certificate51 matches51 rfl rfl
    MergedCutGroups.Batch012.numericValid153 MergedCutGroups.Batch012.numericValid154 MergedCutGroups.Batch012.cellsSound153 MergedCutGroups.Batch012.cellsSound154
    MergedCutGroups.Batch012.cellsNumeric153 MergedCutGroups.Batch012.cellsNumeric154 MergedCutGroups.Batch012.populationMatches153 MergedCutGroups.Batch012.populationMatches154
    PopulationCertificates.Batch005.valid102 PopulationCertificates.Batch005.sound102 WitnessCertificates.Batch005.valid102 WitnessCertificates.Batch005.sound102 CountingCertificates.Batch005.valid102 CountingCertificates.Batch005.sound102
    CutLabelCertificates.Entropy002.valid52 CutLabelCertificates.Minority002.valid51 CutLabelCertificates.Minority002.sound51 H st hI
theorem probabilityBound51 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate153).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate102).dm (WitnessCertificates.Batch005.certificate102).beta) ≤ ((CutFailureCertificates.Budget005.certificate102).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound102 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate102).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate153).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate154).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate102).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate102).bound:ℝ) at hb
  exact (exponentialBound51 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches52 : (MergedCutGroups.Batch013.certificate156).GlobalMatches MergedCutGroups.Batch013.certificate157 CountingCertificates.Batch005.certificate104 CutLabelCertificates.Entropy002.certificate53 CutLabelCertificates.Minority002.certificate52 := by decide +kernel
theorem exponentialBound52 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate156).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate104).dm (WitnessCertificates.Batch005.certificate104).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate104).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch013.certificate156).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch013.certificate157).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate104).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch013.certificate156 MergedCutGroups.Batch013.certificate157 CountingCertificates.Batch005.certificate104 CutLabelCertificates.Entropy002.certificate53 CutLabelCertificates.Minority002.certificate52 matches52 rfl rfl
    MergedCutGroups.Batch013.numericValid156 MergedCutGroups.Batch013.numericValid157 MergedCutGroups.Batch013.cellsSound156 MergedCutGroups.Batch013.cellsSound157
    MergedCutGroups.Batch013.cellsNumeric156 MergedCutGroups.Batch013.cellsNumeric157 MergedCutGroups.Batch013.populationMatches156 MergedCutGroups.Batch013.populationMatches157
    PopulationCertificates.Batch005.valid104 PopulationCertificates.Batch005.sound104 WitnessCertificates.Batch005.valid104 WitnessCertificates.Batch005.sound104 CountingCertificates.Batch005.valid104 CountingCertificates.Batch005.sound104
    CutLabelCertificates.Entropy002.valid53 CutLabelCertificates.Minority002.valid52 CutLabelCertificates.Minority002.sound52 H st hI
theorem probabilityBound52 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate156).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate104).dm (WitnessCertificates.Batch005.certificate104).beta) ≤ ((CutFailureCertificates.Budget005.certificate104).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound104 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate104).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate156).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate157).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate104).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate104).bound:ℝ) at hb
  exact (exponentialBound52 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches53 : (MergedCutGroups.Batch013.certificate159).GlobalMatches MergedCutGroups.Batch013.certificate160 CountingCertificates.Batch005.certificate106 CutLabelCertificates.Entropy002.certificate54 CutLabelCertificates.Minority002.certificate53 := by decide +kernel
theorem exponentialBound53 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate159).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate106).dm (WitnessCertificates.Batch005.certificate106).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate106).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch013.certificate159).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch013.certificate160).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate106).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch013.certificate159 MergedCutGroups.Batch013.certificate160 CountingCertificates.Batch005.certificate106 CutLabelCertificates.Entropy002.certificate54 CutLabelCertificates.Minority002.certificate53 matches53 rfl rfl
    MergedCutGroups.Batch013.numericValid159 MergedCutGroups.Batch013.numericValid160 MergedCutGroups.Batch013.cellsSound159 MergedCutGroups.Batch013.cellsSound160
    MergedCutGroups.Batch013.cellsNumeric159 MergedCutGroups.Batch013.cellsNumeric160 MergedCutGroups.Batch013.populationMatches159 MergedCutGroups.Batch013.populationMatches160
    PopulationCertificates.Batch005.valid106 PopulationCertificates.Batch005.sound106 WitnessCertificates.Batch005.valid106 WitnessCertificates.Batch005.sound106 CountingCertificates.Batch005.valid106 CountingCertificates.Batch005.sound106
    CutLabelCertificates.Entropy002.valid54 CutLabelCertificates.Minority002.valid53 CutLabelCertificates.Minority002.sound53 H st hI
theorem probabilityBound53 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate159).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate106).dm (WitnessCertificates.Batch005.certificate106).beta) ≤ ((CutFailureCertificates.Budget005.certificate106).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound106 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate106).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate159).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate160).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate106).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate106).bound:ℝ) at hb
  exact (exponentialBound53 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches54 : (MergedCutGroups.Batch013.certificate162).GlobalMatches MergedCutGroups.Batch013.certificate163 CountingCertificates.Batch005.certificate108 CutLabelCertificates.Entropy002.certificate55 CutLabelCertificates.Minority002.certificate54 := by decide +kernel
theorem exponentialBound54 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate162).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate108).dm (WitnessCertificates.Batch005.certificate108).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate108).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch013.certificate162).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch013.certificate163).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate108).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch013.certificate162 MergedCutGroups.Batch013.certificate163 CountingCertificates.Batch005.certificate108 CutLabelCertificates.Entropy002.certificate55 CutLabelCertificates.Minority002.certificate54 matches54 rfl rfl
    MergedCutGroups.Batch013.numericValid162 MergedCutGroups.Batch013.numericValid163 MergedCutGroups.Batch013.cellsSound162 MergedCutGroups.Batch013.cellsSound163
    MergedCutGroups.Batch013.cellsNumeric162 MergedCutGroups.Batch013.cellsNumeric163 MergedCutGroups.Batch013.populationMatches162 MergedCutGroups.Batch013.populationMatches163
    PopulationCertificates.Batch005.valid108 PopulationCertificates.Batch005.sound108 WitnessCertificates.Batch005.valid108 WitnessCertificates.Batch005.sound108 CountingCertificates.Batch005.valid108 CountingCertificates.Batch005.sound108
    CutLabelCertificates.Entropy002.valid55 CutLabelCertificates.Minority002.valid54 CutLabelCertificates.Minority002.sound54 H st hI
theorem probabilityBound54 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate162).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate108).dm (WitnessCertificates.Batch005.certificate108).beta) ≤ ((CutFailureCertificates.Budget005.certificate108).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound108 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate108).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate162).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate163).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate108).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate108).bound:ℝ) at hb
  exact (exponentialBound54 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches55 : (MergedCutGroups.Batch013.certificate165).GlobalMatches MergedCutGroups.Batch013.certificate166 CountingCertificates.Batch005.certificate110 CutLabelCertificates.Entropy002.certificate56 CutLabelCertificates.Minority002.certificate55 := by decide +kernel
theorem exponentialBound55 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate165).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate110).dm (WitnessCertificates.Batch005.certificate110).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate110).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch013.certificate165).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch013.certificate166).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate110).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch013.certificate165 MergedCutGroups.Batch013.certificate166 CountingCertificates.Batch005.certificate110 CutLabelCertificates.Entropy002.certificate56 CutLabelCertificates.Minority002.certificate55 matches55 rfl rfl
    MergedCutGroups.Batch013.numericValid165 MergedCutGroups.Batch013.numericValid166 MergedCutGroups.Batch013.cellsSound165 MergedCutGroups.Batch013.cellsSound166
    MergedCutGroups.Batch013.cellsNumeric165 MergedCutGroups.Batch013.cellsNumeric166 MergedCutGroups.Batch013.populationMatches165 MergedCutGroups.Batch013.populationMatches166
    PopulationCertificates.Batch005.valid110 PopulationCertificates.Batch005.sound110 WitnessCertificates.Batch005.valid110 WitnessCertificates.Batch005.sound110 CountingCertificates.Batch005.valid110 CountingCertificates.Batch005.sound110
    CutLabelCertificates.Entropy002.valid56 CutLabelCertificates.Minority002.valid55 CutLabelCertificates.Minority002.sound55 H st hI
theorem probabilityBound55 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate165).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate110).dm (WitnessCertificates.Batch005.certificate110).beta) ≤ ((CutFailureCertificates.Budget005.certificate110).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound110 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate110).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate165).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate166).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate110).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate110).bound:ℝ) at hb
  exact (exponentialBound55 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches56 : (MergedCutGroups.Batch014.certificate168).GlobalMatches MergedCutGroups.Batch014.certificate169 CountingCertificates.Batch005.certificate112 CutLabelCertificates.Entropy002.certificate57 CutLabelCertificates.Minority002.certificate56 := by decide +kernel
theorem exponentialBound56 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate168).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate112).dm (WitnessCertificates.Batch005.certificate112).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate112).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch014.certificate168).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch014.certificate169).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate112).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch014.certificate168 MergedCutGroups.Batch014.certificate169 CountingCertificates.Batch005.certificate112 CutLabelCertificates.Entropy002.certificate57 CutLabelCertificates.Minority002.certificate56 matches56 rfl rfl
    MergedCutGroups.Batch014.numericValid168 MergedCutGroups.Batch014.numericValid169 MergedCutGroups.Batch014.cellsSound168 MergedCutGroups.Batch014.cellsSound169
    MergedCutGroups.Batch014.cellsNumeric168 MergedCutGroups.Batch014.cellsNumeric169 MergedCutGroups.Batch014.populationMatches168 MergedCutGroups.Batch014.populationMatches169
    PopulationCertificates.Batch005.valid112 PopulationCertificates.Batch005.sound112 WitnessCertificates.Batch005.valid112 WitnessCertificates.Batch005.sound112 CountingCertificates.Batch005.valid112 CountingCertificates.Batch005.sound112
    CutLabelCertificates.Entropy002.valid57 CutLabelCertificates.Minority002.valid56 CutLabelCertificates.Minority002.sound56 H st hI
theorem probabilityBound56 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate168).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate112).dm (WitnessCertificates.Batch005.certificate112).beta) ≤ ((CutFailureCertificates.Budget005.certificate112).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound112 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate112).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate168).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate169).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate112).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate112).bound:ℝ) at hb
  exact (exponentialBound56 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches57 : (MergedCutGroups.Batch014.certificate171).GlobalMatches MergedCutGroups.Batch014.certificate172 CountingCertificates.Batch005.certificate114 CutLabelCertificates.Entropy002.certificate58 CutLabelCertificates.Minority002.certificate57 := by decide +kernel
theorem exponentialBound57 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate171).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate114).dm (WitnessCertificates.Batch005.certificate114).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate114).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch014.certificate171).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch014.certificate172).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate114).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch014.certificate171 MergedCutGroups.Batch014.certificate172 CountingCertificates.Batch005.certificate114 CutLabelCertificates.Entropy002.certificate58 CutLabelCertificates.Minority002.certificate57 matches57 rfl rfl
    MergedCutGroups.Batch014.numericValid171 MergedCutGroups.Batch014.numericValid172 MergedCutGroups.Batch014.cellsSound171 MergedCutGroups.Batch014.cellsSound172
    MergedCutGroups.Batch014.cellsNumeric171 MergedCutGroups.Batch014.cellsNumeric172 MergedCutGroups.Batch014.populationMatches171 MergedCutGroups.Batch014.populationMatches172
    PopulationCertificates.Batch005.valid114 PopulationCertificates.Batch005.sound114 WitnessCertificates.Batch005.valid114 WitnessCertificates.Batch005.sound114 CountingCertificates.Batch005.valid114 CountingCertificates.Batch005.sound114
    CutLabelCertificates.Entropy002.valid58 CutLabelCertificates.Minority002.valid57 CutLabelCertificates.Minority002.sound57 H st hI
theorem probabilityBound57 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate171).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate114).dm (WitnessCertificates.Batch005.certificate114).beta) ≤ ((CutFailureCertificates.Budget005.certificate114).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound114 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate114).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate171).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate172).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate114).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate114).bound:ℝ) at hb
  exact (exponentialBound57 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches58 : (MergedCutGroups.Batch014.certificate174).GlobalMatches MergedCutGroups.Batch014.certificate175 CountingCertificates.Batch005.certificate116 CutLabelCertificates.Entropy002.certificate59 CutLabelCertificates.Minority002.certificate58 := by decide +kernel
theorem exponentialBound58 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate174).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate116).dm (WitnessCertificates.Batch005.certificate116).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate116).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch014.certificate174).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch014.certificate175).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate116).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch014.certificate174 MergedCutGroups.Batch014.certificate175 CountingCertificates.Batch005.certificate116 CutLabelCertificates.Entropy002.certificate59 CutLabelCertificates.Minority002.certificate58 matches58 rfl rfl
    MergedCutGroups.Batch014.numericValid174 MergedCutGroups.Batch014.numericValid175 MergedCutGroups.Batch014.cellsSound174 MergedCutGroups.Batch014.cellsSound175
    MergedCutGroups.Batch014.cellsNumeric174 MergedCutGroups.Batch014.cellsNumeric175 MergedCutGroups.Batch014.populationMatches174 MergedCutGroups.Batch014.populationMatches175
    PopulationCertificates.Batch005.valid116 PopulationCertificates.Batch005.sound116 WitnessCertificates.Batch005.valid116 WitnessCertificates.Batch005.sound116 CountingCertificates.Batch005.valid116 CountingCertificates.Batch005.sound116
    CutLabelCertificates.Entropy002.valid59 CutLabelCertificates.Minority002.valid58 CutLabelCertificates.Minority002.sound58 H st hI
theorem probabilityBound58 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate174).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate116).dm (WitnessCertificates.Batch005.certificate116).beta) ≤ ((CutFailureCertificates.Budget005.certificate116).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound116 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate116).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate174).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate175).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate116).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate116).bound:ℝ) at hb
  exact (exponentialBound58 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches59 : (MergedCutGroups.Batch014.certificate177).GlobalMatches MergedCutGroups.Batch014.certificate178 CountingCertificates.Batch005.certificate118 CutLabelCertificates.Entropy003.certificate60 CutLabelCertificates.Minority002.certificate59 := by decide +kernel
theorem exponentialBound59 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate177).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate118).dm (WitnessCertificates.Batch005.certificate118).beta) ≤ (2*exp (-((CountingCertificates.Batch005.certificate118).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch014.certificate177).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch014.certificate178).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch005.certificate118).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch014.certificate177 MergedCutGroups.Batch014.certificate178 CountingCertificates.Batch005.certificate118 CutLabelCertificates.Entropy003.certificate60 CutLabelCertificates.Minority002.certificate59 matches59 rfl rfl
    MergedCutGroups.Batch014.numericValid177 MergedCutGroups.Batch014.numericValid178 MergedCutGroups.Batch014.cellsSound177 MergedCutGroups.Batch014.cellsSound178
    MergedCutGroups.Batch014.cellsNumeric177 MergedCutGroups.Batch014.cellsNumeric178 MergedCutGroups.Batch014.populationMatches177 MergedCutGroups.Batch014.populationMatches178
    PopulationCertificates.Batch005.valid118 PopulationCertificates.Batch005.sound118 WitnessCertificates.Batch005.valid118 WitnessCertificates.Batch005.sound118 CountingCertificates.Batch005.valid118 CountingCertificates.Batch005.sound118
    CutLabelCertificates.Entropy003.valid60 CutLabelCertificates.Minority002.valid59 CutLabelCertificates.Minority002.sound59 H st hI
theorem probabilityBound59 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate177).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch005.certificate118).dm (WitnessCertificates.Batch005.certificate118).beta) ≤ ((CutFailureCertificates.Budget005.certificate118).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound118 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate118).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate177).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate178).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch005.certificate118).omega:ℝ) ≤ ((CutFailureCertificates.Budget005.certificate118).bound:ℝ) at hb
  exact (exponentialBound59 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch002
