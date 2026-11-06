import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch020
import Cycle12.CountingCertificates.Batch021
import Cycle12.CutFailureCertificates.Budget020
import Cycle12.CutFailureCertificates.Budget021
import Cycle12.CutLabelCertificates.Entropy010
import Cycle12.CutLabelCertificates.Entropy011
import Cycle12.CutLabelCertificates.Minority010
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

namespace Cycle12.CertifiedGlobalFailures.Batch010
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches200 : (MergedCutGroups.Batch050.certificate600).GlobalMatches MergedCutGroups.Batch050.certificate601 CountingCertificates.Batch020.certificate400 CutLabelCertificates.Entropy010.certificate201 CutLabelCertificates.Minority010.certificate200 := by decide +kernel
theorem exponentialBound200 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate600).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate400).dm (WitnessCertificates.Batch020.certificate400).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate400).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch050.certificate600).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch050.certificate601).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate400).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch050.certificate600 MergedCutGroups.Batch050.certificate601 CountingCertificates.Batch020.certificate400 CutLabelCertificates.Entropy010.certificate201 CutLabelCertificates.Minority010.certificate200 matches200 rfl rfl
    MergedCutGroups.Batch050.numericValid600 MergedCutGroups.Batch050.numericValid601 MergedCutGroups.Batch050.cellsSound600 MergedCutGroups.Batch050.cellsSound601
    MergedCutGroups.Batch050.cellsNumeric600 MergedCutGroups.Batch050.cellsNumeric601 MergedCutGroups.Batch050.populationMatches600 MergedCutGroups.Batch050.populationMatches601
    PopulationCertificates.Batch020.valid400 PopulationCertificates.Batch020.sound400 WitnessCertificates.Batch020.valid400 WitnessCertificates.Batch020.sound400 CountingCertificates.Batch020.valid400 CountingCertificates.Batch020.sound400
    CutLabelCertificates.Entropy010.valid201 CutLabelCertificates.Minority010.valid200 CutLabelCertificates.Minority010.sound200 H st hI
theorem probabilityBound200 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate600).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate400).dm (WitnessCertificates.Batch020.certificate400).beta) ≤ ((CutFailureCertificates.Budget020.certificate400).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound400 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate400).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate600).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate601).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate400).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate400).bound:ℝ) at hb
  exact (exponentialBound200 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches201 : (MergedCutGroups.Batch050.certificate603).GlobalMatches MergedCutGroups.Batch050.certificate604 CountingCertificates.Batch020.certificate402 CutLabelCertificates.Entropy010.certificate202 CutLabelCertificates.Minority010.certificate201 := by decide +kernel
theorem exponentialBound201 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate603).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate402).dm (WitnessCertificates.Batch020.certificate402).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate402).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch050.certificate603).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch050.certificate604).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate402).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch050.certificate603 MergedCutGroups.Batch050.certificate604 CountingCertificates.Batch020.certificate402 CutLabelCertificates.Entropy010.certificate202 CutLabelCertificates.Minority010.certificate201 matches201 rfl rfl
    MergedCutGroups.Batch050.numericValid603 MergedCutGroups.Batch050.numericValid604 MergedCutGroups.Batch050.cellsSound603 MergedCutGroups.Batch050.cellsSound604
    MergedCutGroups.Batch050.cellsNumeric603 MergedCutGroups.Batch050.cellsNumeric604 MergedCutGroups.Batch050.populationMatches603 MergedCutGroups.Batch050.populationMatches604
    PopulationCertificates.Batch020.valid402 PopulationCertificates.Batch020.sound402 WitnessCertificates.Batch020.valid402 WitnessCertificates.Batch020.sound402 CountingCertificates.Batch020.valid402 CountingCertificates.Batch020.sound402
    CutLabelCertificates.Entropy010.valid202 CutLabelCertificates.Minority010.valid201 CutLabelCertificates.Minority010.sound201 H st hI
theorem probabilityBound201 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate603).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate402).dm (WitnessCertificates.Batch020.certificate402).beta) ≤ ((CutFailureCertificates.Budget020.certificate402).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound402 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate402).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate603).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate604).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate402).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate402).bound:ℝ) at hb
  exact (exponentialBound201 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches202 : (MergedCutGroups.Batch050.certificate606).GlobalMatches MergedCutGroups.Batch050.certificate607 CountingCertificates.Batch020.certificate404 CutLabelCertificates.Entropy010.certificate203 CutLabelCertificates.Minority010.certificate202 := by decide +kernel
theorem exponentialBound202 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate606).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate404).dm (WitnessCertificates.Batch020.certificate404).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate404).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch050.certificate606).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch050.certificate607).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate404).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch050.certificate606 MergedCutGroups.Batch050.certificate607 CountingCertificates.Batch020.certificate404 CutLabelCertificates.Entropy010.certificate203 CutLabelCertificates.Minority010.certificate202 matches202 rfl rfl
    MergedCutGroups.Batch050.numericValid606 MergedCutGroups.Batch050.numericValid607 MergedCutGroups.Batch050.cellsSound606 MergedCutGroups.Batch050.cellsSound607
    MergedCutGroups.Batch050.cellsNumeric606 MergedCutGroups.Batch050.cellsNumeric607 MergedCutGroups.Batch050.populationMatches606 MergedCutGroups.Batch050.populationMatches607
    PopulationCertificates.Batch020.valid404 PopulationCertificates.Batch020.sound404 WitnessCertificates.Batch020.valid404 WitnessCertificates.Batch020.sound404 CountingCertificates.Batch020.valid404 CountingCertificates.Batch020.sound404
    CutLabelCertificates.Entropy010.valid203 CutLabelCertificates.Minority010.valid202 CutLabelCertificates.Minority010.sound202 H st hI
theorem probabilityBound202 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate606).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate404).dm (WitnessCertificates.Batch020.certificate404).beta) ≤ ((CutFailureCertificates.Budget020.certificate404).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound404 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate404).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate606).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate607).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate404).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate404).bound:ℝ) at hb
  exact (exponentialBound202 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches203 : (MergedCutGroups.Batch050.certificate609).GlobalMatches MergedCutGroups.Batch050.certificate610 CountingCertificates.Batch020.certificate406 CutLabelCertificates.Entropy010.certificate204 CutLabelCertificates.Minority010.certificate203 := by decide +kernel
theorem exponentialBound203 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate609).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate406).dm (WitnessCertificates.Batch020.certificate406).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate406).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch050.certificate609).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch050.certificate610).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate406).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch050.certificate609 MergedCutGroups.Batch050.certificate610 CountingCertificates.Batch020.certificate406 CutLabelCertificates.Entropy010.certificate204 CutLabelCertificates.Minority010.certificate203 matches203 rfl rfl
    MergedCutGroups.Batch050.numericValid609 MergedCutGroups.Batch050.numericValid610 MergedCutGroups.Batch050.cellsSound609 MergedCutGroups.Batch050.cellsSound610
    MergedCutGroups.Batch050.cellsNumeric609 MergedCutGroups.Batch050.cellsNumeric610 MergedCutGroups.Batch050.populationMatches609 MergedCutGroups.Batch050.populationMatches610
    PopulationCertificates.Batch020.valid406 PopulationCertificates.Batch020.sound406 WitnessCertificates.Batch020.valid406 WitnessCertificates.Batch020.sound406 CountingCertificates.Batch020.valid406 CountingCertificates.Batch020.sound406
    CutLabelCertificates.Entropy010.valid204 CutLabelCertificates.Minority010.valid203 CutLabelCertificates.Minority010.sound203 H st hI
theorem probabilityBound203 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate609).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate406).dm (WitnessCertificates.Batch020.certificate406).beta) ≤ ((CutFailureCertificates.Budget020.certificate406).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound406 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate406).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate609).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate610).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate406).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate406).bound:ℝ) at hb
  exact (exponentialBound203 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches204 : (MergedCutGroups.Batch051.certificate612).GlobalMatches MergedCutGroups.Batch051.certificate613 CountingCertificates.Batch020.certificate408 CutLabelCertificates.Entropy010.certificate205 CutLabelCertificates.Minority010.certificate204 := by decide +kernel
theorem exponentialBound204 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate612).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate408).dm (WitnessCertificates.Batch020.certificate408).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate408).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch051.certificate612).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch051.certificate613).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate408).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch051.certificate612 MergedCutGroups.Batch051.certificate613 CountingCertificates.Batch020.certificate408 CutLabelCertificates.Entropy010.certificate205 CutLabelCertificates.Minority010.certificate204 matches204 rfl rfl
    MergedCutGroups.Batch051.numericValid612 MergedCutGroups.Batch051.numericValid613 MergedCutGroups.Batch051.cellsSound612 MergedCutGroups.Batch051.cellsSound613
    MergedCutGroups.Batch051.cellsNumeric612 MergedCutGroups.Batch051.cellsNumeric613 MergedCutGroups.Batch051.populationMatches612 MergedCutGroups.Batch051.populationMatches613
    PopulationCertificates.Batch020.valid408 PopulationCertificates.Batch020.sound408 WitnessCertificates.Batch020.valid408 WitnessCertificates.Batch020.sound408 CountingCertificates.Batch020.valid408 CountingCertificates.Batch020.sound408
    CutLabelCertificates.Entropy010.valid205 CutLabelCertificates.Minority010.valid204 CutLabelCertificates.Minority010.sound204 H st hI
theorem probabilityBound204 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate612).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate408).dm (WitnessCertificates.Batch020.certificate408).beta) ≤ ((CutFailureCertificates.Budget020.certificate408).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound408 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate408).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate612).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate613).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate408).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate408).bound:ℝ) at hb
  exact (exponentialBound204 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches205 : (MergedCutGroups.Batch051.certificate615).GlobalMatches MergedCutGroups.Batch051.certificate616 CountingCertificates.Batch020.certificate410 CutLabelCertificates.Entropy010.certificate206 CutLabelCertificates.Minority010.certificate205 := by decide +kernel
theorem exponentialBound205 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate615).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate410).dm (WitnessCertificates.Batch020.certificate410).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate410).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch051.certificate615).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch051.certificate616).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate410).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch051.certificate615 MergedCutGroups.Batch051.certificate616 CountingCertificates.Batch020.certificate410 CutLabelCertificates.Entropy010.certificate206 CutLabelCertificates.Minority010.certificate205 matches205 rfl rfl
    MergedCutGroups.Batch051.numericValid615 MergedCutGroups.Batch051.numericValid616 MergedCutGroups.Batch051.cellsSound615 MergedCutGroups.Batch051.cellsSound616
    MergedCutGroups.Batch051.cellsNumeric615 MergedCutGroups.Batch051.cellsNumeric616 MergedCutGroups.Batch051.populationMatches615 MergedCutGroups.Batch051.populationMatches616
    PopulationCertificates.Batch020.valid410 PopulationCertificates.Batch020.sound410 WitnessCertificates.Batch020.valid410 WitnessCertificates.Batch020.sound410 CountingCertificates.Batch020.valid410 CountingCertificates.Batch020.sound410
    CutLabelCertificates.Entropy010.valid206 CutLabelCertificates.Minority010.valid205 CutLabelCertificates.Minority010.sound205 H st hI
theorem probabilityBound205 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate615).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate410).dm (WitnessCertificates.Batch020.certificate410).beta) ≤ ((CutFailureCertificates.Budget020.certificate410).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound410 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate410).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate615).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate616).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate410).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate410).bound:ℝ) at hb
  exact (exponentialBound205 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches206 : (MergedCutGroups.Batch051.certificate618).GlobalMatches MergedCutGroups.Batch051.certificate619 CountingCertificates.Batch020.certificate412 CutLabelCertificates.Entropy010.certificate207 CutLabelCertificates.Minority010.certificate206 := by decide +kernel
theorem exponentialBound206 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate618).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate412).dm (WitnessCertificates.Batch020.certificate412).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate412).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch051.certificate618).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch051.certificate619).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate412).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch051.certificate618 MergedCutGroups.Batch051.certificate619 CountingCertificates.Batch020.certificate412 CutLabelCertificates.Entropy010.certificate207 CutLabelCertificates.Minority010.certificate206 matches206 rfl rfl
    MergedCutGroups.Batch051.numericValid618 MergedCutGroups.Batch051.numericValid619 MergedCutGroups.Batch051.cellsSound618 MergedCutGroups.Batch051.cellsSound619
    MergedCutGroups.Batch051.cellsNumeric618 MergedCutGroups.Batch051.cellsNumeric619 MergedCutGroups.Batch051.populationMatches618 MergedCutGroups.Batch051.populationMatches619
    PopulationCertificates.Batch020.valid412 PopulationCertificates.Batch020.sound412 WitnessCertificates.Batch020.valid412 WitnessCertificates.Batch020.sound412 CountingCertificates.Batch020.valid412 CountingCertificates.Batch020.sound412
    CutLabelCertificates.Entropy010.valid207 CutLabelCertificates.Minority010.valid206 CutLabelCertificates.Minority010.sound206 H st hI
theorem probabilityBound206 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate618).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate412).dm (WitnessCertificates.Batch020.certificate412).beta) ≤ ((CutFailureCertificates.Budget020.certificate412).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound412 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate412).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate618).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate619).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate412).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate412).bound:ℝ) at hb
  exact (exponentialBound206 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches207 : (MergedCutGroups.Batch051.certificate621).GlobalMatches MergedCutGroups.Batch051.certificate622 CountingCertificates.Batch020.certificate414 CutLabelCertificates.Entropy010.certificate208 CutLabelCertificates.Minority010.certificate207 := by decide +kernel
theorem exponentialBound207 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate621).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate414).dm (WitnessCertificates.Batch020.certificate414).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate414).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch051.certificate621).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch051.certificate622).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate414).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch051.certificate621 MergedCutGroups.Batch051.certificate622 CountingCertificates.Batch020.certificate414 CutLabelCertificates.Entropy010.certificate208 CutLabelCertificates.Minority010.certificate207 matches207 rfl rfl
    MergedCutGroups.Batch051.numericValid621 MergedCutGroups.Batch051.numericValid622 MergedCutGroups.Batch051.cellsSound621 MergedCutGroups.Batch051.cellsSound622
    MergedCutGroups.Batch051.cellsNumeric621 MergedCutGroups.Batch051.cellsNumeric622 MergedCutGroups.Batch051.populationMatches621 MergedCutGroups.Batch051.populationMatches622
    PopulationCertificates.Batch020.valid414 PopulationCertificates.Batch020.sound414 WitnessCertificates.Batch020.valid414 WitnessCertificates.Batch020.sound414 CountingCertificates.Batch020.valid414 CountingCertificates.Batch020.sound414
    CutLabelCertificates.Entropy010.valid208 CutLabelCertificates.Minority010.valid207 CutLabelCertificates.Minority010.sound207 H st hI
theorem probabilityBound207 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate621).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate414).dm (WitnessCertificates.Batch020.certificate414).beta) ≤ ((CutFailureCertificates.Budget020.certificate414).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound414 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate414).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate621).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate622).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate414).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate414).bound:ℝ) at hb
  exact (exponentialBound207 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches208 : (MergedCutGroups.Batch052.certificate624).GlobalMatches MergedCutGroups.Batch052.certificate625 CountingCertificates.Batch020.certificate416 CutLabelCertificates.Entropy010.certificate209 CutLabelCertificates.Minority010.certificate208 := by decide +kernel
theorem exponentialBound208 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate624).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate416).dm (WitnessCertificates.Batch020.certificate416).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate416).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch052.certificate624).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch052.certificate625).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate416).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch052.certificate624 MergedCutGroups.Batch052.certificate625 CountingCertificates.Batch020.certificate416 CutLabelCertificates.Entropy010.certificate209 CutLabelCertificates.Minority010.certificate208 matches208 rfl rfl
    MergedCutGroups.Batch052.numericValid624 MergedCutGroups.Batch052.numericValid625 MergedCutGroups.Batch052.cellsSound624 MergedCutGroups.Batch052.cellsSound625
    MergedCutGroups.Batch052.cellsNumeric624 MergedCutGroups.Batch052.cellsNumeric625 MergedCutGroups.Batch052.populationMatches624 MergedCutGroups.Batch052.populationMatches625
    PopulationCertificates.Batch020.valid416 PopulationCertificates.Batch020.sound416 WitnessCertificates.Batch020.valid416 WitnessCertificates.Batch020.sound416 CountingCertificates.Batch020.valid416 CountingCertificates.Batch020.sound416
    CutLabelCertificates.Entropy010.valid209 CutLabelCertificates.Minority010.valid208 CutLabelCertificates.Minority010.sound208 H st hI
theorem probabilityBound208 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate624).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate416).dm (WitnessCertificates.Batch020.certificate416).beta) ≤ ((CutFailureCertificates.Budget020.certificate416).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound416 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate416).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate624).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate625).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate416).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate416).bound:ℝ) at hb
  exact (exponentialBound208 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches209 : (MergedCutGroups.Batch052.certificate627).GlobalMatches MergedCutGroups.Batch052.certificate628 CountingCertificates.Batch020.certificate418 CutLabelCertificates.Entropy010.certificate210 CutLabelCertificates.Minority010.certificate209 := by decide +kernel
theorem exponentialBound209 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate627).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate418).dm (WitnessCertificates.Batch020.certificate418).beta) ≤ (2*exp (-((CountingCertificates.Batch020.certificate418).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch052.certificate627).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch052.certificate628).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch020.certificate418).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch052.certificate627 MergedCutGroups.Batch052.certificate628 CountingCertificates.Batch020.certificate418 CutLabelCertificates.Entropy010.certificate210 CutLabelCertificates.Minority010.certificate209 matches209 rfl rfl
    MergedCutGroups.Batch052.numericValid627 MergedCutGroups.Batch052.numericValid628 MergedCutGroups.Batch052.cellsSound627 MergedCutGroups.Batch052.cellsSound628
    MergedCutGroups.Batch052.cellsNumeric627 MergedCutGroups.Batch052.cellsNumeric628 MergedCutGroups.Batch052.populationMatches627 MergedCutGroups.Batch052.populationMatches628
    PopulationCertificates.Batch020.valid418 PopulationCertificates.Batch020.sound418 WitnessCertificates.Batch020.valid418 WitnessCertificates.Batch020.sound418 CountingCertificates.Batch020.valid418 CountingCertificates.Batch020.sound418
    CutLabelCertificates.Entropy010.valid210 CutLabelCertificates.Minority010.valid209 CutLabelCertificates.Minority010.sound209 H st hI
theorem probabilityBound209 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate627).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch020.certificate418).dm (WitnessCertificates.Batch020.certificate418).beta) ≤ ((CutFailureCertificates.Budget020.certificate418).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound418 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate418).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate627).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate628).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch020.certificate418).omega:ℝ) ≤ ((CutFailureCertificates.Budget020.certificate418).bound:ℝ) at hb
  exact (exponentialBound209 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches210 : (MergedCutGroups.Batch052.certificate630).GlobalMatches MergedCutGroups.Batch052.certificate631 CountingCertificates.Batch021.certificate420 CutLabelCertificates.Entropy010.certificate211 CutLabelCertificates.Minority010.certificate210 := by decide +kernel
theorem exponentialBound210 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate630).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate420).dm (WitnessCertificates.Batch021.certificate420).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate420).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch052.certificate630).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch052.certificate631).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate420).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch052.certificate630 MergedCutGroups.Batch052.certificate631 CountingCertificates.Batch021.certificate420 CutLabelCertificates.Entropy010.certificate211 CutLabelCertificates.Minority010.certificate210 matches210 rfl rfl
    MergedCutGroups.Batch052.numericValid630 MergedCutGroups.Batch052.numericValid631 MergedCutGroups.Batch052.cellsSound630 MergedCutGroups.Batch052.cellsSound631
    MergedCutGroups.Batch052.cellsNumeric630 MergedCutGroups.Batch052.cellsNumeric631 MergedCutGroups.Batch052.populationMatches630 MergedCutGroups.Batch052.populationMatches631
    PopulationCertificates.Batch021.valid420 PopulationCertificates.Batch021.sound420 WitnessCertificates.Batch021.valid420 WitnessCertificates.Batch021.sound420 CountingCertificates.Batch021.valid420 CountingCertificates.Batch021.sound420
    CutLabelCertificates.Entropy010.valid211 CutLabelCertificates.Minority010.valid210 CutLabelCertificates.Minority010.sound210 H st hI
theorem probabilityBound210 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate630).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate420).dm (WitnessCertificates.Batch021.certificate420).beta) ≤ ((CutFailureCertificates.Budget021.certificate420).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound420 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate420).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate630).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate631).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate420).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate420).bound:ℝ) at hb
  exact (exponentialBound210 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches211 : (MergedCutGroups.Batch052.certificate633).GlobalMatches MergedCutGroups.Batch052.certificate634 CountingCertificates.Batch021.certificate422 CutLabelCertificates.Entropy010.certificate212 CutLabelCertificates.Minority010.certificate211 := by decide +kernel
theorem exponentialBound211 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate633).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate422).dm (WitnessCertificates.Batch021.certificate422).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate422).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch052.certificate633).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch052.certificate634).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate422).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch052.certificate633 MergedCutGroups.Batch052.certificate634 CountingCertificates.Batch021.certificate422 CutLabelCertificates.Entropy010.certificate212 CutLabelCertificates.Minority010.certificate211 matches211 rfl rfl
    MergedCutGroups.Batch052.numericValid633 MergedCutGroups.Batch052.numericValid634 MergedCutGroups.Batch052.cellsSound633 MergedCutGroups.Batch052.cellsSound634
    MergedCutGroups.Batch052.cellsNumeric633 MergedCutGroups.Batch052.cellsNumeric634 MergedCutGroups.Batch052.populationMatches633 MergedCutGroups.Batch052.populationMatches634
    PopulationCertificates.Batch021.valid422 PopulationCertificates.Batch021.sound422 WitnessCertificates.Batch021.valid422 WitnessCertificates.Batch021.sound422 CountingCertificates.Batch021.valid422 CountingCertificates.Batch021.sound422
    CutLabelCertificates.Entropy010.valid212 CutLabelCertificates.Minority010.valid211 CutLabelCertificates.Minority010.sound211 H st hI
theorem probabilityBound211 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate633).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate422).dm (WitnessCertificates.Batch021.certificate422).beta) ≤ ((CutFailureCertificates.Budget021.certificate422).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound422 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate422).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate633).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate634).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate422).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate422).bound:ℝ) at hb
  exact (exponentialBound211 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches212 : (MergedCutGroups.Batch053.certificate636).GlobalMatches MergedCutGroups.Batch053.certificate637 CountingCertificates.Batch021.certificate424 CutLabelCertificates.Entropy010.certificate213 CutLabelCertificates.Minority010.certificate212 := by decide +kernel
theorem exponentialBound212 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate636).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate424).dm (WitnessCertificates.Batch021.certificate424).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate424).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch053.certificate636).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch053.certificate637).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate424).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch053.certificate636 MergedCutGroups.Batch053.certificate637 CountingCertificates.Batch021.certificate424 CutLabelCertificates.Entropy010.certificate213 CutLabelCertificates.Minority010.certificate212 matches212 rfl rfl
    MergedCutGroups.Batch053.numericValid636 MergedCutGroups.Batch053.numericValid637 MergedCutGroups.Batch053.cellsSound636 MergedCutGroups.Batch053.cellsSound637
    MergedCutGroups.Batch053.cellsNumeric636 MergedCutGroups.Batch053.cellsNumeric637 MergedCutGroups.Batch053.populationMatches636 MergedCutGroups.Batch053.populationMatches637
    PopulationCertificates.Batch021.valid424 PopulationCertificates.Batch021.sound424 WitnessCertificates.Batch021.valid424 WitnessCertificates.Batch021.sound424 CountingCertificates.Batch021.valid424 CountingCertificates.Batch021.sound424
    CutLabelCertificates.Entropy010.valid213 CutLabelCertificates.Minority010.valid212 CutLabelCertificates.Minority010.sound212 H st hI
theorem probabilityBound212 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate636).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate424).dm (WitnessCertificates.Batch021.certificate424).beta) ≤ ((CutFailureCertificates.Budget021.certificate424).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound424 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate424).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate636).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate637).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate424).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate424).bound:ℝ) at hb
  exact (exponentialBound212 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches213 : (MergedCutGroups.Batch053.certificate639).GlobalMatches MergedCutGroups.Batch053.certificate640 CountingCertificates.Batch021.certificate426 CutLabelCertificates.Entropy010.certificate214 CutLabelCertificates.Minority010.certificate213 := by decide +kernel
theorem exponentialBound213 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate639).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate426).dm (WitnessCertificates.Batch021.certificate426).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate426).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch053.certificate639).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch053.certificate640).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate426).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch053.certificate639 MergedCutGroups.Batch053.certificate640 CountingCertificates.Batch021.certificate426 CutLabelCertificates.Entropy010.certificate214 CutLabelCertificates.Minority010.certificate213 matches213 rfl rfl
    MergedCutGroups.Batch053.numericValid639 MergedCutGroups.Batch053.numericValid640 MergedCutGroups.Batch053.cellsSound639 MergedCutGroups.Batch053.cellsSound640
    MergedCutGroups.Batch053.cellsNumeric639 MergedCutGroups.Batch053.cellsNumeric640 MergedCutGroups.Batch053.populationMatches639 MergedCutGroups.Batch053.populationMatches640
    PopulationCertificates.Batch021.valid426 PopulationCertificates.Batch021.sound426 WitnessCertificates.Batch021.valid426 WitnessCertificates.Batch021.sound426 CountingCertificates.Batch021.valid426 CountingCertificates.Batch021.sound426
    CutLabelCertificates.Entropy010.valid214 CutLabelCertificates.Minority010.valid213 CutLabelCertificates.Minority010.sound213 H st hI
theorem probabilityBound213 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate639).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate426).dm (WitnessCertificates.Batch021.certificate426).beta) ≤ ((CutFailureCertificates.Budget021.certificate426).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound426 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate426).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate639).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate640).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate426).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate426).bound:ℝ) at hb
  exact (exponentialBound213 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches214 : (MergedCutGroups.Batch053.certificate642).GlobalMatches MergedCutGroups.Batch053.certificate643 CountingCertificates.Batch021.certificate428 CutLabelCertificates.Entropy010.certificate215 CutLabelCertificates.Minority010.certificate214 := by decide +kernel
theorem exponentialBound214 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate642).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate428).dm (WitnessCertificates.Batch021.certificate428).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate428).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch053.certificate642).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch053.certificate643).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate428).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch053.certificate642 MergedCutGroups.Batch053.certificate643 CountingCertificates.Batch021.certificate428 CutLabelCertificates.Entropy010.certificate215 CutLabelCertificates.Minority010.certificate214 matches214 rfl rfl
    MergedCutGroups.Batch053.numericValid642 MergedCutGroups.Batch053.numericValid643 MergedCutGroups.Batch053.cellsSound642 MergedCutGroups.Batch053.cellsSound643
    MergedCutGroups.Batch053.cellsNumeric642 MergedCutGroups.Batch053.cellsNumeric643 MergedCutGroups.Batch053.populationMatches642 MergedCutGroups.Batch053.populationMatches643
    PopulationCertificates.Batch021.valid428 PopulationCertificates.Batch021.sound428 WitnessCertificates.Batch021.valid428 WitnessCertificates.Batch021.sound428 CountingCertificates.Batch021.valid428 CountingCertificates.Batch021.sound428
    CutLabelCertificates.Entropy010.valid215 CutLabelCertificates.Minority010.valid214 CutLabelCertificates.Minority010.sound214 H st hI
theorem probabilityBound214 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate642).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate428).dm (WitnessCertificates.Batch021.certificate428).beta) ≤ ((CutFailureCertificates.Budget021.certificate428).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound428 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate428).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate642).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate643).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate428).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate428).bound:ℝ) at hb
  exact (exponentialBound214 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches215 : (MergedCutGroups.Batch053.certificate645).GlobalMatches MergedCutGroups.Batch053.certificate646 CountingCertificates.Batch021.certificate430 CutLabelCertificates.Entropy010.certificate216 CutLabelCertificates.Minority010.certificate215 := by decide +kernel
theorem exponentialBound215 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate645).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate430).dm (WitnessCertificates.Batch021.certificate430).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate430).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch053.certificate645).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch053.certificate646).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate430).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch053.certificate645 MergedCutGroups.Batch053.certificate646 CountingCertificates.Batch021.certificate430 CutLabelCertificates.Entropy010.certificate216 CutLabelCertificates.Minority010.certificate215 matches215 rfl rfl
    MergedCutGroups.Batch053.numericValid645 MergedCutGroups.Batch053.numericValid646 MergedCutGroups.Batch053.cellsSound645 MergedCutGroups.Batch053.cellsSound646
    MergedCutGroups.Batch053.cellsNumeric645 MergedCutGroups.Batch053.cellsNumeric646 MergedCutGroups.Batch053.populationMatches645 MergedCutGroups.Batch053.populationMatches646
    PopulationCertificates.Batch021.valid430 PopulationCertificates.Batch021.sound430 WitnessCertificates.Batch021.valid430 WitnessCertificates.Batch021.sound430 CountingCertificates.Batch021.valid430 CountingCertificates.Batch021.sound430
    CutLabelCertificates.Entropy010.valid216 CutLabelCertificates.Minority010.valid215 CutLabelCertificates.Minority010.sound215 H st hI
theorem probabilityBound215 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate645).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate430).dm (WitnessCertificates.Batch021.certificate430).beta) ≤ ((CutFailureCertificates.Budget021.certificate430).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound430 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate430).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate645).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate646).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate430).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate430).bound:ℝ) at hb
  exact (exponentialBound215 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches216 : (MergedCutGroups.Batch054.certificate648).GlobalMatches MergedCutGroups.Batch054.certificate649 CountingCertificates.Batch021.certificate432 CutLabelCertificates.Entropy010.certificate217 CutLabelCertificates.Minority010.certificate216 := by decide +kernel
theorem exponentialBound216 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate648).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate432).dm (WitnessCertificates.Batch021.certificate432).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate432).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch054.certificate648).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch054.certificate649).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate432).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch054.certificate648 MergedCutGroups.Batch054.certificate649 CountingCertificates.Batch021.certificate432 CutLabelCertificates.Entropy010.certificate217 CutLabelCertificates.Minority010.certificate216 matches216 rfl rfl
    MergedCutGroups.Batch054.numericValid648 MergedCutGroups.Batch054.numericValid649 MergedCutGroups.Batch054.cellsSound648 MergedCutGroups.Batch054.cellsSound649
    MergedCutGroups.Batch054.cellsNumeric648 MergedCutGroups.Batch054.cellsNumeric649 MergedCutGroups.Batch054.populationMatches648 MergedCutGroups.Batch054.populationMatches649
    PopulationCertificates.Batch021.valid432 PopulationCertificates.Batch021.sound432 WitnessCertificates.Batch021.valid432 WitnessCertificates.Batch021.sound432 CountingCertificates.Batch021.valid432 CountingCertificates.Batch021.sound432
    CutLabelCertificates.Entropy010.valid217 CutLabelCertificates.Minority010.valid216 CutLabelCertificates.Minority010.sound216 H st hI
theorem probabilityBound216 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate648).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate432).dm (WitnessCertificates.Batch021.certificate432).beta) ≤ ((CutFailureCertificates.Budget021.certificate432).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound432 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate432).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate648).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate649).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate432).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate432).bound:ℝ) at hb
  exact (exponentialBound216 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches217 : (MergedCutGroups.Batch054.certificate651).GlobalMatches MergedCutGroups.Batch054.certificate652 CountingCertificates.Batch021.certificate434 CutLabelCertificates.Entropy010.certificate218 CutLabelCertificates.Minority010.certificate217 := by decide +kernel
theorem exponentialBound217 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate651).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate434).dm (WitnessCertificates.Batch021.certificate434).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate434).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch054.certificate651).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch054.certificate652).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate434).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch054.certificate651 MergedCutGroups.Batch054.certificate652 CountingCertificates.Batch021.certificate434 CutLabelCertificates.Entropy010.certificate218 CutLabelCertificates.Minority010.certificate217 matches217 rfl rfl
    MergedCutGroups.Batch054.numericValid651 MergedCutGroups.Batch054.numericValid652 MergedCutGroups.Batch054.cellsSound651 MergedCutGroups.Batch054.cellsSound652
    MergedCutGroups.Batch054.cellsNumeric651 MergedCutGroups.Batch054.cellsNumeric652 MergedCutGroups.Batch054.populationMatches651 MergedCutGroups.Batch054.populationMatches652
    PopulationCertificates.Batch021.valid434 PopulationCertificates.Batch021.sound434 WitnessCertificates.Batch021.valid434 WitnessCertificates.Batch021.sound434 CountingCertificates.Batch021.valid434 CountingCertificates.Batch021.sound434
    CutLabelCertificates.Entropy010.valid218 CutLabelCertificates.Minority010.valid217 CutLabelCertificates.Minority010.sound217 H st hI
theorem probabilityBound217 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate651).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate434).dm (WitnessCertificates.Batch021.certificate434).beta) ≤ ((CutFailureCertificates.Budget021.certificate434).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound434 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate434).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate651).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate652).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate434).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate434).bound:ℝ) at hb
  exact (exponentialBound217 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches218 : (MergedCutGroups.Batch054.certificate654).GlobalMatches MergedCutGroups.Batch054.certificate655 CountingCertificates.Batch021.certificate436 CutLabelCertificates.Entropy010.certificate219 CutLabelCertificates.Minority010.certificate218 := by decide +kernel
theorem exponentialBound218 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate654).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate436).dm (WitnessCertificates.Batch021.certificate436).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate436).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch054.certificate654).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch054.certificate655).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate436).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch054.certificate654 MergedCutGroups.Batch054.certificate655 CountingCertificates.Batch021.certificate436 CutLabelCertificates.Entropy010.certificate219 CutLabelCertificates.Minority010.certificate218 matches218 rfl rfl
    MergedCutGroups.Batch054.numericValid654 MergedCutGroups.Batch054.numericValid655 MergedCutGroups.Batch054.cellsSound654 MergedCutGroups.Batch054.cellsSound655
    MergedCutGroups.Batch054.cellsNumeric654 MergedCutGroups.Batch054.cellsNumeric655 MergedCutGroups.Batch054.populationMatches654 MergedCutGroups.Batch054.populationMatches655
    PopulationCertificates.Batch021.valid436 PopulationCertificates.Batch021.sound436 WitnessCertificates.Batch021.valid436 WitnessCertificates.Batch021.sound436 CountingCertificates.Batch021.valid436 CountingCertificates.Batch021.sound436
    CutLabelCertificates.Entropy010.valid219 CutLabelCertificates.Minority010.valid218 CutLabelCertificates.Minority010.sound218 H st hI
theorem probabilityBound218 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate654).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate436).dm (WitnessCertificates.Batch021.certificate436).beta) ≤ ((CutFailureCertificates.Budget021.certificate436).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound436 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate436).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate654).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate655).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate436).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate436).bound:ℝ) at hb
  exact (exponentialBound218 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches219 : (MergedCutGroups.Batch054.certificate657).GlobalMatches MergedCutGroups.Batch054.certificate658 CountingCertificates.Batch021.certificate438 CutLabelCertificates.Entropy011.certificate220 CutLabelCertificates.Minority010.certificate219 := by decide +kernel
theorem exponentialBound219 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate657).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate438).dm (WitnessCertificates.Batch021.certificate438).beta) ≤ (2*exp (-((CountingCertificates.Batch021.certificate438).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch054.certificate657).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch054.certificate658).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch021.certificate438).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch054.certificate657 MergedCutGroups.Batch054.certificate658 CountingCertificates.Batch021.certificate438 CutLabelCertificates.Entropy011.certificate220 CutLabelCertificates.Minority010.certificate219 matches219 rfl rfl
    MergedCutGroups.Batch054.numericValid657 MergedCutGroups.Batch054.numericValid658 MergedCutGroups.Batch054.cellsSound657 MergedCutGroups.Batch054.cellsSound658
    MergedCutGroups.Batch054.cellsNumeric657 MergedCutGroups.Batch054.cellsNumeric658 MergedCutGroups.Batch054.populationMatches657 MergedCutGroups.Batch054.populationMatches658
    PopulationCertificates.Batch021.valid438 PopulationCertificates.Batch021.sound438 WitnessCertificates.Batch021.valid438 WitnessCertificates.Batch021.sound438 CountingCertificates.Batch021.valid438 CountingCertificates.Batch021.sound438
    CutLabelCertificates.Entropy011.valid220 CutLabelCertificates.Minority010.valid219 CutLabelCertificates.Minority010.sound219 H st hI
theorem probabilityBound219 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate657).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch021.certificate438).dm (WitnessCertificates.Batch021.certificate438).beta) ≤ ((CutFailureCertificates.Budget021.certificate438).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound438 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate438).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate657).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate658).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch021.certificate438).omega:ℝ) ≤ ((CutFailureCertificates.Budget021.certificate438).bound:ℝ) at hb
  exact (exponentialBound219 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch010
