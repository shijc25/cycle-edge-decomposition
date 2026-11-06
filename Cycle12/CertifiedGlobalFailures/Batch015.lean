import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch030
import Cycle12.CountingCertificates.Batch031
import Cycle12.CutFailureCertificates.Budget030
import Cycle12.CutFailureCertificates.Budget031
import Cycle12.CutLabelCertificates.Entropy015
import Cycle12.CutLabelCertificates.Entropy016
import Cycle12.CutLabelCertificates.Minority015
import Cycle12.MergedCutGroups.Batch075
import Cycle12.MergedCutGroups.Batch076
import Cycle12.MergedCutGroups.Batch077
import Cycle12.MergedCutGroups.Batch078
import Cycle12.MergedCutGroups.Batch079
import Cycle12.PopulationCertificates.Batch030
import Cycle12.PopulationCertificates.Batch031
import Cycle12.WitnessCertificates.Batch030
import Cycle12.WitnessCertificates.Batch031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch015
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches300 : (MergedCutGroups.Batch075.certificate900).GlobalMatches MergedCutGroups.Batch075.certificate901 CountingCertificates.Batch030.certificate600 CutLabelCertificates.Entropy015.certificate301 CutLabelCertificates.Minority015.certificate300 := by decide +kernel
theorem exponentialBound300 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate900).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate600).dm (WitnessCertificates.Batch030.certificate600).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate600).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch075.certificate900).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch075.certificate901).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate600).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch075.certificate900 MergedCutGroups.Batch075.certificate901 CountingCertificates.Batch030.certificate600 CutLabelCertificates.Entropy015.certificate301 CutLabelCertificates.Minority015.certificate300 matches300 rfl rfl
    MergedCutGroups.Batch075.numericValid900 MergedCutGroups.Batch075.numericValid901 MergedCutGroups.Batch075.cellsSound900 MergedCutGroups.Batch075.cellsSound901
    MergedCutGroups.Batch075.cellsNumeric900 MergedCutGroups.Batch075.cellsNumeric901 MergedCutGroups.Batch075.populationMatches900 MergedCutGroups.Batch075.populationMatches901
    PopulationCertificates.Batch030.valid600 PopulationCertificates.Batch030.sound600 WitnessCertificates.Batch030.valid600 WitnessCertificates.Batch030.sound600 CountingCertificates.Batch030.valid600 CountingCertificates.Batch030.sound600
    CutLabelCertificates.Entropy015.valid301 CutLabelCertificates.Minority015.valid300 CutLabelCertificates.Minority015.sound300 H st hI
theorem probabilityBound300 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate900).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate600).dm (WitnessCertificates.Batch030.certificate600).beta) ≤ ((CutFailureCertificates.Budget030.certificate600).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound600 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate600).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate900).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate901).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate600).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate600).bound:ℝ) at hb
  exact (exponentialBound300 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches301 : (MergedCutGroups.Batch075.certificate903).GlobalMatches MergedCutGroups.Batch075.certificate904 CountingCertificates.Batch030.certificate602 CutLabelCertificates.Entropy015.certificate302 CutLabelCertificates.Minority015.certificate301 := by decide +kernel
theorem exponentialBound301 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate903).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate602).dm (WitnessCertificates.Batch030.certificate602).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate602).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch075.certificate903).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch075.certificate904).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate602).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch075.certificate903 MergedCutGroups.Batch075.certificate904 CountingCertificates.Batch030.certificate602 CutLabelCertificates.Entropy015.certificate302 CutLabelCertificates.Minority015.certificate301 matches301 rfl rfl
    MergedCutGroups.Batch075.numericValid903 MergedCutGroups.Batch075.numericValid904 MergedCutGroups.Batch075.cellsSound903 MergedCutGroups.Batch075.cellsSound904
    MergedCutGroups.Batch075.cellsNumeric903 MergedCutGroups.Batch075.cellsNumeric904 MergedCutGroups.Batch075.populationMatches903 MergedCutGroups.Batch075.populationMatches904
    PopulationCertificates.Batch030.valid602 PopulationCertificates.Batch030.sound602 WitnessCertificates.Batch030.valid602 WitnessCertificates.Batch030.sound602 CountingCertificates.Batch030.valid602 CountingCertificates.Batch030.sound602
    CutLabelCertificates.Entropy015.valid302 CutLabelCertificates.Minority015.valid301 CutLabelCertificates.Minority015.sound301 H st hI
theorem probabilityBound301 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate903).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate602).dm (WitnessCertificates.Batch030.certificate602).beta) ≤ ((CutFailureCertificates.Budget030.certificate602).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound602 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate602).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate903).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate904).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate602).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate602).bound:ℝ) at hb
  exact (exponentialBound301 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches302 : (MergedCutGroups.Batch075.certificate906).GlobalMatches MergedCutGroups.Batch075.certificate907 CountingCertificates.Batch030.certificate604 CutLabelCertificates.Entropy015.certificate303 CutLabelCertificates.Minority015.certificate302 := by decide +kernel
theorem exponentialBound302 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate906).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate604).dm (WitnessCertificates.Batch030.certificate604).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate604).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch075.certificate906).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch075.certificate907).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate604).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch075.certificate906 MergedCutGroups.Batch075.certificate907 CountingCertificates.Batch030.certificate604 CutLabelCertificates.Entropy015.certificate303 CutLabelCertificates.Minority015.certificate302 matches302 rfl rfl
    MergedCutGroups.Batch075.numericValid906 MergedCutGroups.Batch075.numericValid907 MergedCutGroups.Batch075.cellsSound906 MergedCutGroups.Batch075.cellsSound907
    MergedCutGroups.Batch075.cellsNumeric906 MergedCutGroups.Batch075.cellsNumeric907 MergedCutGroups.Batch075.populationMatches906 MergedCutGroups.Batch075.populationMatches907
    PopulationCertificates.Batch030.valid604 PopulationCertificates.Batch030.sound604 WitnessCertificates.Batch030.valid604 WitnessCertificates.Batch030.sound604 CountingCertificates.Batch030.valid604 CountingCertificates.Batch030.sound604
    CutLabelCertificates.Entropy015.valid303 CutLabelCertificates.Minority015.valid302 CutLabelCertificates.Minority015.sound302 H st hI
theorem probabilityBound302 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate906).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate604).dm (WitnessCertificates.Batch030.certificate604).beta) ≤ ((CutFailureCertificates.Budget030.certificate604).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound604 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate604).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate906).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate907).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate604).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate604).bound:ℝ) at hb
  exact (exponentialBound302 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches303 : (MergedCutGroups.Batch075.certificate909).GlobalMatches MergedCutGroups.Batch075.certificate910 CountingCertificates.Batch030.certificate606 CutLabelCertificates.Entropy015.certificate304 CutLabelCertificates.Minority015.certificate303 := by decide +kernel
theorem exponentialBound303 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate909).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate606).dm (WitnessCertificates.Batch030.certificate606).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate606).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch075.certificate909).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch075.certificate910).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate606).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch075.certificate909 MergedCutGroups.Batch075.certificate910 CountingCertificates.Batch030.certificate606 CutLabelCertificates.Entropy015.certificate304 CutLabelCertificates.Minority015.certificate303 matches303 rfl rfl
    MergedCutGroups.Batch075.numericValid909 MergedCutGroups.Batch075.numericValid910 MergedCutGroups.Batch075.cellsSound909 MergedCutGroups.Batch075.cellsSound910
    MergedCutGroups.Batch075.cellsNumeric909 MergedCutGroups.Batch075.cellsNumeric910 MergedCutGroups.Batch075.populationMatches909 MergedCutGroups.Batch075.populationMatches910
    PopulationCertificates.Batch030.valid606 PopulationCertificates.Batch030.sound606 WitnessCertificates.Batch030.valid606 WitnessCertificates.Batch030.sound606 CountingCertificates.Batch030.valid606 CountingCertificates.Batch030.sound606
    CutLabelCertificates.Entropy015.valid304 CutLabelCertificates.Minority015.valid303 CutLabelCertificates.Minority015.sound303 H st hI
theorem probabilityBound303 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate909).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate606).dm (WitnessCertificates.Batch030.certificate606).beta) ≤ ((CutFailureCertificates.Budget030.certificate606).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound606 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate606).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate909).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate910).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate606).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate606).bound:ℝ) at hb
  exact (exponentialBound303 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches304 : (MergedCutGroups.Batch076.certificate912).GlobalMatches MergedCutGroups.Batch076.certificate913 CountingCertificates.Batch030.certificate608 CutLabelCertificates.Entropy015.certificate305 CutLabelCertificates.Minority015.certificate304 := by decide +kernel
theorem exponentialBound304 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate912).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate608).dm (WitnessCertificates.Batch030.certificate608).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate608).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch076.certificate912).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch076.certificate913).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate608).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch076.certificate912 MergedCutGroups.Batch076.certificate913 CountingCertificates.Batch030.certificate608 CutLabelCertificates.Entropy015.certificate305 CutLabelCertificates.Minority015.certificate304 matches304 rfl rfl
    MergedCutGroups.Batch076.numericValid912 MergedCutGroups.Batch076.numericValid913 MergedCutGroups.Batch076.cellsSound912 MergedCutGroups.Batch076.cellsSound913
    MergedCutGroups.Batch076.cellsNumeric912 MergedCutGroups.Batch076.cellsNumeric913 MergedCutGroups.Batch076.populationMatches912 MergedCutGroups.Batch076.populationMatches913
    PopulationCertificates.Batch030.valid608 PopulationCertificates.Batch030.sound608 WitnessCertificates.Batch030.valid608 WitnessCertificates.Batch030.sound608 CountingCertificates.Batch030.valid608 CountingCertificates.Batch030.sound608
    CutLabelCertificates.Entropy015.valid305 CutLabelCertificates.Minority015.valid304 CutLabelCertificates.Minority015.sound304 H st hI
theorem probabilityBound304 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate912).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate608).dm (WitnessCertificates.Batch030.certificate608).beta) ≤ ((CutFailureCertificates.Budget030.certificate608).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound608 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate608).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate912).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate913).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate608).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate608).bound:ℝ) at hb
  exact (exponentialBound304 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches305 : (MergedCutGroups.Batch076.certificate915).GlobalMatches MergedCutGroups.Batch076.certificate916 CountingCertificates.Batch030.certificate610 CutLabelCertificates.Entropy015.certificate306 CutLabelCertificates.Minority015.certificate305 := by decide +kernel
theorem exponentialBound305 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate915).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate610).dm (WitnessCertificates.Batch030.certificate610).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate610).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch076.certificate915).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch076.certificate916).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate610).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch076.certificate915 MergedCutGroups.Batch076.certificate916 CountingCertificates.Batch030.certificate610 CutLabelCertificates.Entropy015.certificate306 CutLabelCertificates.Minority015.certificate305 matches305 rfl rfl
    MergedCutGroups.Batch076.numericValid915 MergedCutGroups.Batch076.numericValid916 MergedCutGroups.Batch076.cellsSound915 MergedCutGroups.Batch076.cellsSound916
    MergedCutGroups.Batch076.cellsNumeric915 MergedCutGroups.Batch076.cellsNumeric916 MergedCutGroups.Batch076.populationMatches915 MergedCutGroups.Batch076.populationMatches916
    PopulationCertificates.Batch030.valid610 PopulationCertificates.Batch030.sound610 WitnessCertificates.Batch030.valid610 WitnessCertificates.Batch030.sound610 CountingCertificates.Batch030.valid610 CountingCertificates.Batch030.sound610
    CutLabelCertificates.Entropy015.valid306 CutLabelCertificates.Minority015.valid305 CutLabelCertificates.Minority015.sound305 H st hI
theorem probabilityBound305 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate915).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate610).dm (WitnessCertificates.Batch030.certificate610).beta) ≤ ((CutFailureCertificates.Budget030.certificate610).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound610 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate610).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate915).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate916).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate610).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate610).bound:ℝ) at hb
  exact (exponentialBound305 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches306 : (MergedCutGroups.Batch076.certificate918).GlobalMatches MergedCutGroups.Batch076.certificate919 CountingCertificates.Batch030.certificate612 CutLabelCertificates.Entropy015.certificate307 CutLabelCertificates.Minority015.certificate306 := by decide +kernel
theorem exponentialBound306 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate918).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate612).dm (WitnessCertificates.Batch030.certificate612).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate612).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch076.certificate918).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch076.certificate919).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate612).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch076.certificate918 MergedCutGroups.Batch076.certificate919 CountingCertificates.Batch030.certificate612 CutLabelCertificates.Entropy015.certificate307 CutLabelCertificates.Minority015.certificate306 matches306 rfl rfl
    MergedCutGroups.Batch076.numericValid918 MergedCutGroups.Batch076.numericValid919 MergedCutGroups.Batch076.cellsSound918 MergedCutGroups.Batch076.cellsSound919
    MergedCutGroups.Batch076.cellsNumeric918 MergedCutGroups.Batch076.cellsNumeric919 MergedCutGroups.Batch076.populationMatches918 MergedCutGroups.Batch076.populationMatches919
    PopulationCertificates.Batch030.valid612 PopulationCertificates.Batch030.sound612 WitnessCertificates.Batch030.valid612 WitnessCertificates.Batch030.sound612 CountingCertificates.Batch030.valid612 CountingCertificates.Batch030.sound612
    CutLabelCertificates.Entropy015.valid307 CutLabelCertificates.Minority015.valid306 CutLabelCertificates.Minority015.sound306 H st hI
theorem probabilityBound306 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate918).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate612).dm (WitnessCertificates.Batch030.certificate612).beta) ≤ ((CutFailureCertificates.Budget030.certificate612).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound612 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate612).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate918).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate919).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate612).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate612).bound:ℝ) at hb
  exact (exponentialBound306 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches307 : (MergedCutGroups.Batch076.certificate921).GlobalMatches MergedCutGroups.Batch076.certificate922 CountingCertificates.Batch030.certificate614 CutLabelCertificates.Entropy015.certificate308 CutLabelCertificates.Minority015.certificate307 := by decide +kernel
theorem exponentialBound307 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate921).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate614).dm (WitnessCertificates.Batch030.certificate614).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate614).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch076.certificate921).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch076.certificate922).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate614).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch076.certificate921 MergedCutGroups.Batch076.certificate922 CountingCertificates.Batch030.certificate614 CutLabelCertificates.Entropy015.certificate308 CutLabelCertificates.Minority015.certificate307 matches307 rfl rfl
    MergedCutGroups.Batch076.numericValid921 MergedCutGroups.Batch076.numericValid922 MergedCutGroups.Batch076.cellsSound921 MergedCutGroups.Batch076.cellsSound922
    MergedCutGroups.Batch076.cellsNumeric921 MergedCutGroups.Batch076.cellsNumeric922 MergedCutGroups.Batch076.populationMatches921 MergedCutGroups.Batch076.populationMatches922
    PopulationCertificates.Batch030.valid614 PopulationCertificates.Batch030.sound614 WitnessCertificates.Batch030.valid614 WitnessCertificates.Batch030.sound614 CountingCertificates.Batch030.valid614 CountingCertificates.Batch030.sound614
    CutLabelCertificates.Entropy015.valid308 CutLabelCertificates.Minority015.valid307 CutLabelCertificates.Minority015.sound307 H st hI
theorem probabilityBound307 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate921).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate614).dm (WitnessCertificates.Batch030.certificate614).beta) ≤ ((CutFailureCertificates.Budget030.certificate614).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound614 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate614).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate921).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate922).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate614).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate614).bound:ℝ) at hb
  exact (exponentialBound307 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches308 : (MergedCutGroups.Batch077.certificate924).GlobalMatches MergedCutGroups.Batch077.certificate925 CountingCertificates.Batch030.certificate616 CutLabelCertificates.Entropy015.certificate309 CutLabelCertificates.Minority015.certificate308 := by decide +kernel
theorem exponentialBound308 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate924).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate616).dm (WitnessCertificates.Batch030.certificate616).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate616).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch077.certificate924).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch077.certificate925).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate616).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch077.certificate924 MergedCutGroups.Batch077.certificate925 CountingCertificates.Batch030.certificate616 CutLabelCertificates.Entropy015.certificate309 CutLabelCertificates.Minority015.certificate308 matches308 rfl rfl
    MergedCutGroups.Batch077.numericValid924 MergedCutGroups.Batch077.numericValid925 MergedCutGroups.Batch077.cellsSound924 MergedCutGroups.Batch077.cellsSound925
    MergedCutGroups.Batch077.cellsNumeric924 MergedCutGroups.Batch077.cellsNumeric925 MergedCutGroups.Batch077.populationMatches924 MergedCutGroups.Batch077.populationMatches925
    PopulationCertificates.Batch030.valid616 PopulationCertificates.Batch030.sound616 WitnessCertificates.Batch030.valid616 WitnessCertificates.Batch030.sound616 CountingCertificates.Batch030.valid616 CountingCertificates.Batch030.sound616
    CutLabelCertificates.Entropy015.valid309 CutLabelCertificates.Minority015.valid308 CutLabelCertificates.Minority015.sound308 H st hI
theorem probabilityBound308 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate924).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate616).dm (WitnessCertificates.Batch030.certificate616).beta) ≤ ((CutFailureCertificates.Budget030.certificate616).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound616 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate616).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate924).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate925).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate616).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate616).bound:ℝ) at hb
  exact (exponentialBound308 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches309 : (MergedCutGroups.Batch077.certificate927).GlobalMatches MergedCutGroups.Batch077.certificate928 CountingCertificates.Batch030.certificate618 CutLabelCertificates.Entropy015.certificate310 CutLabelCertificates.Minority015.certificate309 := by decide +kernel
theorem exponentialBound309 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate927).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate618).dm (WitnessCertificates.Batch030.certificate618).beta) ≤ (2*exp (-((CountingCertificates.Batch030.certificate618).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch077.certificate927).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch077.certificate928).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch030.certificate618).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch077.certificate927 MergedCutGroups.Batch077.certificate928 CountingCertificates.Batch030.certificate618 CutLabelCertificates.Entropy015.certificate310 CutLabelCertificates.Minority015.certificate309 matches309 rfl rfl
    MergedCutGroups.Batch077.numericValid927 MergedCutGroups.Batch077.numericValid928 MergedCutGroups.Batch077.cellsSound927 MergedCutGroups.Batch077.cellsSound928
    MergedCutGroups.Batch077.cellsNumeric927 MergedCutGroups.Batch077.cellsNumeric928 MergedCutGroups.Batch077.populationMatches927 MergedCutGroups.Batch077.populationMatches928
    PopulationCertificates.Batch030.valid618 PopulationCertificates.Batch030.sound618 WitnessCertificates.Batch030.valid618 WitnessCertificates.Batch030.sound618 CountingCertificates.Batch030.valid618 CountingCertificates.Batch030.sound618
    CutLabelCertificates.Entropy015.valid310 CutLabelCertificates.Minority015.valid309 CutLabelCertificates.Minority015.sound309 H st hI
theorem probabilityBound309 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate927).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch030.certificate618).dm (WitnessCertificates.Batch030.certificate618).beta) ≤ ((CutFailureCertificates.Budget030.certificate618).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound618 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate618).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate927).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate928).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch030.certificate618).omega:ℝ) ≤ ((CutFailureCertificates.Budget030.certificate618).bound:ℝ) at hb
  exact (exponentialBound309 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches310 : (MergedCutGroups.Batch077.certificate930).GlobalMatches MergedCutGroups.Batch077.certificate931 CountingCertificates.Batch031.certificate620 CutLabelCertificates.Entropy015.certificate311 CutLabelCertificates.Minority015.certificate310 := by decide +kernel
theorem exponentialBound310 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate930).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate620).dm (WitnessCertificates.Batch031.certificate620).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate620).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch077.certificate930).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch077.certificate931).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate620).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch077.certificate930 MergedCutGroups.Batch077.certificate931 CountingCertificates.Batch031.certificate620 CutLabelCertificates.Entropy015.certificate311 CutLabelCertificates.Minority015.certificate310 matches310 rfl rfl
    MergedCutGroups.Batch077.numericValid930 MergedCutGroups.Batch077.numericValid931 MergedCutGroups.Batch077.cellsSound930 MergedCutGroups.Batch077.cellsSound931
    MergedCutGroups.Batch077.cellsNumeric930 MergedCutGroups.Batch077.cellsNumeric931 MergedCutGroups.Batch077.populationMatches930 MergedCutGroups.Batch077.populationMatches931
    PopulationCertificates.Batch031.valid620 PopulationCertificates.Batch031.sound620 WitnessCertificates.Batch031.valid620 WitnessCertificates.Batch031.sound620 CountingCertificates.Batch031.valid620 CountingCertificates.Batch031.sound620
    CutLabelCertificates.Entropy015.valid311 CutLabelCertificates.Minority015.valid310 CutLabelCertificates.Minority015.sound310 H st hI
theorem probabilityBound310 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate930).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate620).dm (WitnessCertificates.Batch031.certificate620).beta) ≤ ((CutFailureCertificates.Budget031.certificate620).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound620 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate620).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate930).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate931).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate620).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate620).bound:ℝ) at hb
  exact (exponentialBound310 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches311 : (MergedCutGroups.Batch077.certificate933).GlobalMatches MergedCutGroups.Batch077.certificate934 CountingCertificates.Batch031.certificate622 CutLabelCertificates.Entropy015.certificate312 CutLabelCertificates.Minority015.certificate311 := by decide +kernel
theorem exponentialBound311 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate933).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate622).dm (WitnessCertificates.Batch031.certificate622).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate622).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch077.certificate933).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch077.certificate934).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate622).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch077.certificate933 MergedCutGroups.Batch077.certificate934 CountingCertificates.Batch031.certificate622 CutLabelCertificates.Entropy015.certificate312 CutLabelCertificates.Minority015.certificate311 matches311 rfl rfl
    MergedCutGroups.Batch077.numericValid933 MergedCutGroups.Batch077.numericValid934 MergedCutGroups.Batch077.cellsSound933 MergedCutGroups.Batch077.cellsSound934
    MergedCutGroups.Batch077.cellsNumeric933 MergedCutGroups.Batch077.cellsNumeric934 MergedCutGroups.Batch077.populationMatches933 MergedCutGroups.Batch077.populationMatches934
    PopulationCertificates.Batch031.valid622 PopulationCertificates.Batch031.sound622 WitnessCertificates.Batch031.valid622 WitnessCertificates.Batch031.sound622 CountingCertificates.Batch031.valid622 CountingCertificates.Batch031.sound622
    CutLabelCertificates.Entropy015.valid312 CutLabelCertificates.Minority015.valid311 CutLabelCertificates.Minority015.sound311 H st hI
theorem probabilityBound311 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate933).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate622).dm (WitnessCertificates.Batch031.certificate622).beta) ≤ ((CutFailureCertificates.Budget031.certificate622).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound622 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate622).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate933).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate934).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate622).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate622).bound:ℝ) at hb
  exact (exponentialBound311 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches312 : (MergedCutGroups.Batch078.certificate936).GlobalMatches MergedCutGroups.Batch078.certificate937 CountingCertificates.Batch031.certificate624 CutLabelCertificates.Entropy015.certificate313 CutLabelCertificates.Minority015.certificate312 := by decide +kernel
theorem exponentialBound312 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate936).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate624).dm (WitnessCertificates.Batch031.certificate624).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate624).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch078.certificate936).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch078.certificate937).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate624).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch078.certificate936 MergedCutGroups.Batch078.certificate937 CountingCertificates.Batch031.certificate624 CutLabelCertificates.Entropy015.certificate313 CutLabelCertificates.Minority015.certificate312 matches312 rfl rfl
    MergedCutGroups.Batch078.numericValid936 MergedCutGroups.Batch078.numericValid937 MergedCutGroups.Batch078.cellsSound936 MergedCutGroups.Batch078.cellsSound937
    MergedCutGroups.Batch078.cellsNumeric936 MergedCutGroups.Batch078.cellsNumeric937 MergedCutGroups.Batch078.populationMatches936 MergedCutGroups.Batch078.populationMatches937
    PopulationCertificates.Batch031.valid624 PopulationCertificates.Batch031.sound624 WitnessCertificates.Batch031.valid624 WitnessCertificates.Batch031.sound624 CountingCertificates.Batch031.valid624 CountingCertificates.Batch031.sound624
    CutLabelCertificates.Entropy015.valid313 CutLabelCertificates.Minority015.valid312 CutLabelCertificates.Minority015.sound312 H st hI
theorem probabilityBound312 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate936).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate624).dm (WitnessCertificates.Batch031.certificate624).beta) ≤ ((CutFailureCertificates.Budget031.certificate624).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound624 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate624).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate936).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate937).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate624).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate624).bound:ℝ) at hb
  exact (exponentialBound312 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches313 : (MergedCutGroups.Batch078.certificate939).GlobalMatches MergedCutGroups.Batch078.certificate940 CountingCertificates.Batch031.certificate626 CutLabelCertificates.Entropy015.certificate314 CutLabelCertificates.Minority015.certificate313 := by decide +kernel
theorem exponentialBound313 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate939).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate626).dm (WitnessCertificates.Batch031.certificate626).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate626).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch078.certificate939).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch078.certificate940).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate626).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch078.certificate939 MergedCutGroups.Batch078.certificate940 CountingCertificates.Batch031.certificate626 CutLabelCertificates.Entropy015.certificate314 CutLabelCertificates.Minority015.certificate313 matches313 rfl rfl
    MergedCutGroups.Batch078.numericValid939 MergedCutGroups.Batch078.numericValid940 MergedCutGroups.Batch078.cellsSound939 MergedCutGroups.Batch078.cellsSound940
    MergedCutGroups.Batch078.cellsNumeric939 MergedCutGroups.Batch078.cellsNumeric940 MergedCutGroups.Batch078.populationMatches939 MergedCutGroups.Batch078.populationMatches940
    PopulationCertificates.Batch031.valid626 PopulationCertificates.Batch031.sound626 WitnessCertificates.Batch031.valid626 WitnessCertificates.Batch031.sound626 CountingCertificates.Batch031.valid626 CountingCertificates.Batch031.sound626
    CutLabelCertificates.Entropy015.valid314 CutLabelCertificates.Minority015.valid313 CutLabelCertificates.Minority015.sound313 H st hI
theorem probabilityBound313 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate939).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate626).dm (WitnessCertificates.Batch031.certificate626).beta) ≤ ((CutFailureCertificates.Budget031.certificate626).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound626 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate626).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate939).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate940).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate626).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate626).bound:ℝ) at hb
  exact (exponentialBound313 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches314 : (MergedCutGroups.Batch078.certificate942).GlobalMatches MergedCutGroups.Batch078.certificate943 CountingCertificates.Batch031.certificate628 CutLabelCertificates.Entropy015.certificate315 CutLabelCertificates.Minority015.certificate314 := by decide +kernel
theorem exponentialBound314 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate942).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate628).dm (WitnessCertificates.Batch031.certificate628).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate628).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch078.certificate942).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch078.certificate943).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate628).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch078.certificate942 MergedCutGroups.Batch078.certificate943 CountingCertificates.Batch031.certificate628 CutLabelCertificates.Entropy015.certificate315 CutLabelCertificates.Minority015.certificate314 matches314 rfl rfl
    MergedCutGroups.Batch078.numericValid942 MergedCutGroups.Batch078.numericValid943 MergedCutGroups.Batch078.cellsSound942 MergedCutGroups.Batch078.cellsSound943
    MergedCutGroups.Batch078.cellsNumeric942 MergedCutGroups.Batch078.cellsNumeric943 MergedCutGroups.Batch078.populationMatches942 MergedCutGroups.Batch078.populationMatches943
    PopulationCertificates.Batch031.valid628 PopulationCertificates.Batch031.sound628 WitnessCertificates.Batch031.valid628 WitnessCertificates.Batch031.sound628 CountingCertificates.Batch031.valid628 CountingCertificates.Batch031.sound628
    CutLabelCertificates.Entropy015.valid315 CutLabelCertificates.Minority015.valid314 CutLabelCertificates.Minority015.sound314 H st hI
theorem probabilityBound314 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate942).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate628).dm (WitnessCertificates.Batch031.certificate628).beta) ≤ ((CutFailureCertificates.Budget031.certificate628).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound628 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate628).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate942).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate943).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate628).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate628).bound:ℝ) at hb
  exact (exponentialBound314 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches315 : (MergedCutGroups.Batch078.certificate945).GlobalMatches MergedCutGroups.Batch078.certificate946 CountingCertificates.Batch031.certificate630 CutLabelCertificates.Entropy015.certificate316 CutLabelCertificates.Minority015.certificate315 := by decide +kernel
theorem exponentialBound315 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate945).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate630).dm (WitnessCertificates.Batch031.certificate630).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate630).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch078.certificate945).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch078.certificate946).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate630).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch078.certificate945 MergedCutGroups.Batch078.certificate946 CountingCertificates.Batch031.certificate630 CutLabelCertificates.Entropy015.certificate316 CutLabelCertificates.Minority015.certificate315 matches315 rfl rfl
    MergedCutGroups.Batch078.numericValid945 MergedCutGroups.Batch078.numericValid946 MergedCutGroups.Batch078.cellsSound945 MergedCutGroups.Batch078.cellsSound946
    MergedCutGroups.Batch078.cellsNumeric945 MergedCutGroups.Batch078.cellsNumeric946 MergedCutGroups.Batch078.populationMatches945 MergedCutGroups.Batch078.populationMatches946
    PopulationCertificates.Batch031.valid630 PopulationCertificates.Batch031.sound630 WitnessCertificates.Batch031.valid630 WitnessCertificates.Batch031.sound630 CountingCertificates.Batch031.valid630 CountingCertificates.Batch031.sound630
    CutLabelCertificates.Entropy015.valid316 CutLabelCertificates.Minority015.valid315 CutLabelCertificates.Minority015.sound315 H st hI
theorem probabilityBound315 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate945).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate630).dm (WitnessCertificates.Batch031.certificate630).beta) ≤ ((CutFailureCertificates.Budget031.certificate630).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound630 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate630).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate945).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate946).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate630).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate630).bound:ℝ) at hb
  exact (exponentialBound315 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches316 : (MergedCutGroups.Batch079.certificate948).GlobalMatches MergedCutGroups.Batch079.certificate949 CountingCertificates.Batch031.certificate632 CutLabelCertificates.Entropy015.certificate317 CutLabelCertificates.Minority015.certificate316 := by decide +kernel
theorem exponentialBound316 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate948).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate632).dm (WitnessCertificates.Batch031.certificate632).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate632).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch079.certificate948).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch079.certificate949).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate632).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch079.certificate948 MergedCutGroups.Batch079.certificate949 CountingCertificates.Batch031.certificate632 CutLabelCertificates.Entropy015.certificate317 CutLabelCertificates.Minority015.certificate316 matches316 rfl rfl
    MergedCutGroups.Batch079.numericValid948 MergedCutGroups.Batch079.numericValid949 MergedCutGroups.Batch079.cellsSound948 MergedCutGroups.Batch079.cellsSound949
    MergedCutGroups.Batch079.cellsNumeric948 MergedCutGroups.Batch079.cellsNumeric949 MergedCutGroups.Batch079.populationMatches948 MergedCutGroups.Batch079.populationMatches949
    PopulationCertificates.Batch031.valid632 PopulationCertificates.Batch031.sound632 WitnessCertificates.Batch031.valid632 WitnessCertificates.Batch031.sound632 CountingCertificates.Batch031.valid632 CountingCertificates.Batch031.sound632
    CutLabelCertificates.Entropy015.valid317 CutLabelCertificates.Minority015.valid316 CutLabelCertificates.Minority015.sound316 H st hI
theorem probabilityBound316 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate948).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate632).dm (WitnessCertificates.Batch031.certificate632).beta) ≤ ((CutFailureCertificates.Budget031.certificate632).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound632 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate632).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate948).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate949).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate632).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate632).bound:ℝ) at hb
  exact (exponentialBound316 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches317 : (MergedCutGroups.Batch079.certificate951).GlobalMatches MergedCutGroups.Batch079.certificate952 CountingCertificates.Batch031.certificate634 CutLabelCertificates.Entropy015.certificate318 CutLabelCertificates.Minority015.certificate317 := by decide +kernel
theorem exponentialBound317 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate951).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate634).dm (WitnessCertificates.Batch031.certificate634).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate634).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch079.certificate951).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch079.certificate952).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate634).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch079.certificate951 MergedCutGroups.Batch079.certificate952 CountingCertificates.Batch031.certificate634 CutLabelCertificates.Entropy015.certificate318 CutLabelCertificates.Minority015.certificate317 matches317 rfl rfl
    MergedCutGroups.Batch079.numericValid951 MergedCutGroups.Batch079.numericValid952 MergedCutGroups.Batch079.cellsSound951 MergedCutGroups.Batch079.cellsSound952
    MergedCutGroups.Batch079.cellsNumeric951 MergedCutGroups.Batch079.cellsNumeric952 MergedCutGroups.Batch079.populationMatches951 MergedCutGroups.Batch079.populationMatches952
    PopulationCertificates.Batch031.valid634 PopulationCertificates.Batch031.sound634 WitnessCertificates.Batch031.valid634 WitnessCertificates.Batch031.sound634 CountingCertificates.Batch031.valid634 CountingCertificates.Batch031.sound634
    CutLabelCertificates.Entropy015.valid318 CutLabelCertificates.Minority015.valid317 CutLabelCertificates.Minority015.sound317 H st hI
theorem probabilityBound317 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate951).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate634).dm (WitnessCertificates.Batch031.certificate634).beta) ≤ ((CutFailureCertificates.Budget031.certificate634).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound634 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate634).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate951).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate952).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate634).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate634).bound:ℝ) at hb
  exact (exponentialBound317 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches318 : (MergedCutGroups.Batch079.certificate954).GlobalMatches MergedCutGroups.Batch079.certificate955 CountingCertificates.Batch031.certificate636 CutLabelCertificates.Entropy015.certificate319 CutLabelCertificates.Minority015.certificate318 := by decide +kernel
theorem exponentialBound318 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate954).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate636).dm (WitnessCertificates.Batch031.certificate636).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate636).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch079.certificate954).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch079.certificate955).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate636).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch079.certificate954 MergedCutGroups.Batch079.certificate955 CountingCertificates.Batch031.certificate636 CutLabelCertificates.Entropy015.certificate319 CutLabelCertificates.Minority015.certificate318 matches318 rfl rfl
    MergedCutGroups.Batch079.numericValid954 MergedCutGroups.Batch079.numericValid955 MergedCutGroups.Batch079.cellsSound954 MergedCutGroups.Batch079.cellsSound955
    MergedCutGroups.Batch079.cellsNumeric954 MergedCutGroups.Batch079.cellsNumeric955 MergedCutGroups.Batch079.populationMatches954 MergedCutGroups.Batch079.populationMatches955
    PopulationCertificates.Batch031.valid636 PopulationCertificates.Batch031.sound636 WitnessCertificates.Batch031.valid636 WitnessCertificates.Batch031.sound636 CountingCertificates.Batch031.valid636 CountingCertificates.Batch031.sound636
    CutLabelCertificates.Entropy015.valid319 CutLabelCertificates.Minority015.valid318 CutLabelCertificates.Minority015.sound318 H st hI
theorem probabilityBound318 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate954).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate636).dm (WitnessCertificates.Batch031.certificate636).beta) ≤ ((CutFailureCertificates.Budget031.certificate636).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound636 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate636).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate954).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate955).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate636).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate636).bound:ℝ) at hb
  exact (exponentialBound318 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches319 : (MergedCutGroups.Batch079.certificate957).GlobalMatches MergedCutGroups.Batch079.certificate958 CountingCertificates.Batch031.certificate638 CutLabelCertificates.Entropy016.certificate320 CutLabelCertificates.Minority015.certificate319 := by decide +kernel
theorem exponentialBound319 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate957).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate638).dm (WitnessCertificates.Batch031.certificate638).beta) ≤ (2*exp (-((CountingCertificates.Batch031.certificate638).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch079.certificate957).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch079.certificate958).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch031.certificate638).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch079.certificate957 MergedCutGroups.Batch079.certificate958 CountingCertificates.Batch031.certificate638 CutLabelCertificates.Entropy016.certificate320 CutLabelCertificates.Minority015.certificate319 matches319 rfl rfl
    MergedCutGroups.Batch079.numericValid957 MergedCutGroups.Batch079.numericValid958 MergedCutGroups.Batch079.cellsSound957 MergedCutGroups.Batch079.cellsSound958
    MergedCutGroups.Batch079.cellsNumeric957 MergedCutGroups.Batch079.cellsNumeric958 MergedCutGroups.Batch079.populationMatches957 MergedCutGroups.Batch079.populationMatches958
    PopulationCertificates.Batch031.valid638 PopulationCertificates.Batch031.sound638 WitnessCertificates.Batch031.valid638 WitnessCertificates.Batch031.sound638 CountingCertificates.Batch031.valid638 CountingCertificates.Batch031.sound638
    CutLabelCertificates.Entropy016.valid320 CutLabelCertificates.Minority015.valid319 CutLabelCertificates.Minority015.sound319 H st hI
theorem probabilityBound319 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate957).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch031.certificate638).dm (WitnessCertificates.Batch031.certificate638).beta) ≤ ((CutFailureCertificates.Budget031.certificate638).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound638 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate638).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate957).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate958).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch031.certificate638).omega:ℝ) ≤ ((CutFailureCertificates.Budget031.certificate638).bound:ℝ) at hb
  exact (exponentialBound319 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch015
