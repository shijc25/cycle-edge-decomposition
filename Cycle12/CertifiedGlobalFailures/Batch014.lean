import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch028
import Cycle12.CountingCertificates.Batch029
import Cycle12.CutFailureCertificates.Budget028
import Cycle12.CutFailureCertificates.Budget029
import Cycle12.CutLabelCertificates.Entropy014
import Cycle12.CutLabelCertificates.Entropy015
import Cycle12.CutLabelCertificates.Minority014
import Cycle12.MergedCutGroups.Batch070
import Cycle12.MergedCutGroups.Batch071
import Cycle12.MergedCutGroups.Batch072
import Cycle12.MergedCutGroups.Batch073
import Cycle12.MergedCutGroups.Batch074
import Cycle12.PopulationCertificates.Batch028
import Cycle12.PopulationCertificates.Batch029
import Cycle12.WitnessCertificates.Batch028
import Cycle12.WitnessCertificates.Batch029

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch014
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches280 : (MergedCutGroups.Batch070.certificate840).GlobalMatches MergedCutGroups.Batch070.certificate841 CountingCertificates.Batch028.certificate560 CutLabelCertificates.Entropy014.certificate281 CutLabelCertificates.Minority014.certificate280 := by decide +kernel
theorem exponentialBound280 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate840).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate560).dm (WitnessCertificates.Batch028.certificate560).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate560).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch070.certificate840).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch070.certificate841).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate560).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch070.certificate840 MergedCutGroups.Batch070.certificate841 CountingCertificates.Batch028.certificate560 CutLabelCertificates.Entropy014.certificate281 CutLabelCertificates.Minority014.certificate280 matches280 rfl rfl
    MergedCutGroups.Batch070.numericValid840 MergedCutGroups.Batch070.numericValid841 MergedCutGroups.Batch070.cellsSound840 MergedCutGroups.Batch070.cellsSound841
    MergedCutGroups.Batch070.cellsNumeric840 MergedCutGroups.Batch070.cellsNumeric841 MergedCutGroups.Batch070.populationMatches840 MergedCutGroups.Batch070.populationMatches841
    PopulationCertificates.Batch028.valid560 PopulationCertificates.Batch028.sound560 WitnessCertificates.Batch028.valid560 WitnessCertificates.Batch028.sound560 CountingCertificates.Batch028.valid560 CountingCertificates.Batch028.sound560
    CutLabelCertificates.Entropy014.valid281 CutLabelCertificates.Minority014.valid280 CutLabelCertificates.Minority014.sound280 H st hI
theorem probabilityBound280 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate840).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate560).dm (WitnessCertificates.Batch028.certificate560).beta) ≤ ((CutFailureCertificates.Budget028.certificate560).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound560 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate560).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate840).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate841).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate560).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate560).bound:ℝ) at hb
  exact (exponentialBound280 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches281 : (MergedCutGroups.Batch070.certificate843).GlobalMatches MergedCutGroups.Batch070.certificate844 CountingCertificates.Batch028.certificate562 CutLabelCertificates.Entropy014.certificate282 CutLabelCertificates.Minority014.certificate281 := by decide +kernel
theorem exponentialBound281 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate843).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate562).dm (WitnessCertificates.Batch028.certificate562).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate562).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch070.certificate843).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch070.certificate844).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate562).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch070.certificate843 MergedCutGroups.Batch070.certificate844 CountingCertificates.Batch028.certificate562 CutLabelCertificates.Entropy014.certificate282 CutLabelCertificates.Minority014.certificate281 matches281 rfl rfl
    MergedCutGroups.Batch070.numericValid843 MergedCutGroups.Batch070.numericValid844 MergedCutGroups.Batch070.cellsSound843 MergedCutGroups.Batch070.cellsSound844
    MergedCutGroups.Batch070.cellsNumeric843 MergedCutGroups.Batch070.cellsNumeric844 MergedCutGroups.Batch070.populationMatches843 MergedCutGroups.Batch070.populationMatches844
    PopulationCertificates.Batch028.valid562 PopulationCertificates.Batch028.sound562 WitnessCertificates.Batch028.valid562 WitnessCertificates.Batch028.sound562 CountingCertificates.Batch028.valid562 CountingCertificates.Batch028.sound562
    CutLabelCertificates.Entropy014.valid282 CutLabelCertificates.Minority014.valid281 CutLabelCertificates.Minority014.sound281 H st hI
theorem probabilityBound281 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate843).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate562).dm (WitnessCertificates.Batch028.certificate562).beta) ≤ ((CutFailureCertificates.Budget028.certificate562).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound562 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate562).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate843).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate844).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate562).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate562).bound:ℝ) at hb
  exact (exponentialBound281 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches282 : (MergedCutGroups.Batch070.certificate846).GlobalMatches MergedCutGroups.Batch070.certificate847 CountingCertificates.Batch028.certificate564 CutLabelCertificates.Entropy014.certificate283 CutLabelCertificates.Minority014.certificate282 := by decide +kernel
theorem exponentialBound282 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate846).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate564).dm (WitnessCertificates.Batch028.certificate564).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate564).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch070.certificate846).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch070.certificate847).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate564).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch070.certificate846 MergedCutGroups.Batch070.certificate847 CountingCertificates.Batch028.certificate564 CutLabelCertificates.Entropy014.certificate283 CutLabelCertificates.Minority014.certificate282 matches282 rfl rfl
    MergedCutGroups.Batch070.numericValid846 MergedCutGroups.Batch070.numericValid847 MergedCutGroups.Batch070.cellsSound846 MergedCutGroups.Batch070.cellsSound847
    MergedCutGroups.Batch070.cellsNumeric846 MergedCutGroups.Batch070.cellsNumeric847 MergedCutGroups.Batch070.populationMatches846 MergedCutGroups.Batch070.populationMatches847
    PopulationCertificates.Batch028.valid564 PopulationCertificates.Batch028.sound564 WitnessCertificates.Batch028.valid564 WitnessCertificates.Batch028.sound564 CountingCertificates.Batch028.valid564 CountingCertificates.Batch028.sound564
    CutLabelCertificates.Entropy014.valid283 CutLabelCertificates.Minority014.valid282 CutLabelCertificates.Minority014.sound282 H st hI
theorem probabilityBound282 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate846).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate564).dm (WitnessCertificates.Batch028.certificate564).beta) ≤ ((CutFailureCertificates.Budget028.certificate564).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound564 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate564).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate846).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate847).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate564).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate564).bound:ℝ) at hb
  exact (exponentialBound282 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches283 : (MergedCutGroups.Batch070.certificate849).GlobalMatches MergedCutGroups.Batch070.certificate850 CountingCertificates.Batch028.certificate566 CutLabelCertificates.Entropy014.certificate284 CutLabelCertificates.Minority014.certificate283 := by decide +kernel
theorem exponentialBound283 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate849).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate566).dm (WitnessCertificates.Batch028.certificate566).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate566).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch070.certificate849).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch070.certificate850).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate566).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch070.certificate849 MergedCutGroups.Batch070.certificate850 CountingCertificates.Batch028.certificate566 CutLabelCertificates.Entropy014.certificate284 CutLabelCertificates.Minority014.certificate283 matches283 rfl rfl
    MergedCutGroups.Batch070.numericValid849 MergedCutGroups.Batch070.numericValid850 MergedCutGroups.Batch070.cellsSound849 MergedCutGroups.Batch070.cellsSound850
    MergedCutGroups.Batch070.cellsNumeric849 MergedCutGroups.Batch070.cellsNumeric850 MergedCutGroups.Batch070.populationMatches849 MergedCutGroups.Batch070.populationMatches850
    PopulationCertificates.Batch028.valid566 PopulationCertificates.Batch028.sound566 WitnessCertificates.Batch028.valid566 WitnessCertificates.Batch028.sound566 CountingCertificates.Batch028.valid566 CountingCertificates.Batch028.sound566
    CutLabelCertificates.Entropy014.valid284 CutLabelCertificates.Minority014.valid283 CutLabelCertificates.Minority014.sound283 H st hI
theorem probabilityBound283 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate849).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate566).dm (WitnessCertificates.Batch028.certificate566).beta) ≤ ((CutFailureCertificates.Budget028.certificate566).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound566 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate566).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate849).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate850).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate566).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate566).bound:ℝ) at hb
  exact (exponentialBound283 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches284 : (MergedCutGroups.Batch071.certificate852).GlobalMatches MergedCutGroups.Batch071.certificate853 CountingCertificates.Batch028.certificate568 CutLabelCertificates.Entropy014.certificate285 CutLabelCertificates.Minority014.certificate284 := by decide +kernel
theorem exponentialBound284 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate852).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate568).dm (WitnessCertificates.Batch028.certificate568).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate568).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch071.certificate852).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch071.certificate853).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate568).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch071.certificate852 MergedCutGroups.Batch071.certificate853 CountingCertificates.Batch028.certificate568 CutLabelCertificates.Entropy014.certificate285 CutLabelCertificates.Minority014.certificate284 matches284 rfl rfl
    MergedCutGroups.Batch071.numericValid852 MergedCutGroups.Batch071.numericValid853 MergedCutGroups.Batch071.cellsSound852 MergedCutGroups.Batch071.cellsSound853
    MergedCutGroups.Batch071.cellsNumeric852 MergedCutGroups.Batch071.cellsNumeric853 MergedCutGroups.Batch071.populationMatches852 MergedCutGroups.Batch071.populationMatches853
    PopulationCertificates.Batch028.valid568 PopulationCertificates.Batch028.sound568 WitnessCertificates.Batch028.valid568 WitnessCertificates.Batch028.sound568 CountingCertificates.Batch028.valid568 CountingCertificates.Batch028.sound568
    CutLabelCertificates.Entropy014.valid285 CutLabelCertificates.Minority014.valid284 CutLabelCertificates.Minority014.sound284 H st hI
theorem probabilityBound284 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate852).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate568).dm (WitnessCertificates.Batch028.certificate568).beta) ≤ ((CutFailureCertificates.Budget028.certificate568).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound568 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate568).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate852).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate853).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate568).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate568).bound:ℝ) at hb
  exact (exponentialBound284 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches285 : (MergedCutGroups.Batch071.certificate855).GlobalMatches MergedCutGroups.Batch071.certificate856 CountingCertificates.Batch028.certificate570 CutLabelCertificates.Entropy014.certificate286 CutLabelCertificates.Minority014.certificate285 := by decide +kernel
theorem exponentialBound285 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate855).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate570).dm (WitnessCertificates.Batch028.certificate570).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate570).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch071.certificate855).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch071.certificate856).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate570).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch071.certificate855 MergedCutGroups.Batch071.certificate856 CountingCertificates.Batch028.certificate570 CutLabelCertificates.Entropy014.certificate286 CutLabelCertificates.Minority014.certificate285 matches285 rfl rfl
    MergedCutGroups.Batch071.numericValid855 MergedCutGroups.Batch071.numericValid856 MergedCutGroups.Batch071.cellsSound855 MergedCutGroups.Batch071.cellsSound856
    MergedCutGroups.Batch071.cellsNumeric855 MergedCutGroups.Batch071.cellsNumeric856 MergedCutGroups.Batch071.populationMatches855 MergedCutGroups.Batch071.populationMatches856
    PopulationCertificates.Batch028.valid570 PopulationCertificates.Batch028.sound570 WitnessCertificates.Batch028.valid570 WitnessCertificates.Batch028.sound570 CountingCertificates.Batch028.valid570 CountingCertificates.Batch028.sound570
    CutLabelCertificates.Entropy014.valid286 CutLabelCertificates.Minority014.valid285 CutLabelCertificates.Minority014.sound285 H st hI
theorem probabilityBound285 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate855).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate570).dm (WitnessCertificates.Batch028.certificate570).beta) ≤ ((CutFailureCertificates.Budget028.certificate570).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound570 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate570).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate855).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate856).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate570).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate570).bound:ℝ) at hb
  exact (exponentialBound285 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches286 : (MergedCutGroups.Batch071.certificate858).GlobalMatches MergedCutGroups.Batch071.certificate859 CountingCertificates.Batch028.certificate572 CutLabelCertificates.Entropy014.certificate287 CutLabelCertificates.Minority014.certificate286 := by decide +kernel
theorem exponentialBound286 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate858).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate572).dm (WitnessCertificates.Batch028.certificate572).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate572).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch071.certificate858).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch071.certificate859).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate572).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch071.certificate858 MergedCutGroups.Batch071.certificate859 CountingCertificates.Batch028.certificate572 CutLabelCertificates.Entropy014.certificate287 CutLabelCertificates.Minority014.certificate286 matches286 rfl rfl
    MergedCutGroups.Batch071.numericValid858 MergedCutGroups.Batch071.numericValid859 MergedCutGroups.Batch071.cellsSound858 MergedCutGroups.Batch071.cellsSound859
    MergedCutGroups.Batch071.cellsNumeric858 MergedCutGroups.Batch071.cellsNumeric859 MergedCutGroups.Batch071.populationMatches858 MergedCutGroups.Batch071.populationMatches859
    PopulationCertificates.Batch028.valid572 PopulationCertificates.Batch028.sound572 WitnessCertificates.Batch028.valid572 WitnessCertificates.Batch028.sound572 CountingCertificates.Batch028.valid572 CountingCertificates.Batch028.sound572
    CutLabelCertificates.Entropy014.valid287 CutLabelCertificates.Minority014.valid286 CutLabelCertificates.Minority014.sound286 H st hI
theorem probabilityBound286 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate858).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate572).dm (WitnessCertificates.Batch028.certificate572).beta) ≤ ((CutFailureCertificates.Budget028.certificate572).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound572 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate572).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate858).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate859).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate572).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate572).bound:ℝ) at hb
  exact (exponentialBound286 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches287 : (MergedCutGroups.Batch071.certificate861).GlobalMatches MergedCutGroups.Batch071.certificate862 CountingCertificates.Batch028.certificate574 CutLabelCertificates.Entropy014.certificate288 CutLabelCertificates.Minority014.certificate287 := by decide +kernel
theorem exponentialBound287 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate861).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate574).dm (WitnessCertificates.Batch028.certificate574).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate574).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch071.certificate861).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch071.certificate862).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate574).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch071.certificate861 MergedCutGroups.Batch071.certificate862 CountingCertificates.Batch028.certificate574 CutLabelCertificates.Entropy014.certificate288 CutLabelCertificates.Minority014.certificate287 matches287 rfl rfl
    MergedCutGroups.Batch071.numericValid861 MergedCutGroups.Batch071.numericValid862 MergedCutGroups.Batch071.cellsSound861 MergedCutGroups.Batch071.cellsSound862
    MergedCutGroups.Batch071.cellsNumeric861 MergedCutGroups.Batch071.cellsNumeric862 MergedCutGroups.Batch071.populationMatches861 MergedCutGroups.Batch071.populationMatches862
    PopulationCertificates.Batch028.valid574 PopulationCertificates.Batch028.sound574 WitnessCertificates.Batch028.valid574 WitnessCertificates.Batch028.sound574 CountingCertificates.Batch028.valid574 CountingCertificates.Batch028.sound574
    CutLabelCertificates.Entropy014.valid288 CutLabelCertificates.Minority014.valid287 CutLabelCertificates.Minority014.sound287 H st hI
theorem probabilityBound287 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate861).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate574).dm (WitnessCertificates.Batch028.certificate574).beta) ≤ ((CutFailureCertificates.Budget028.certificate574).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound574 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate574).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate861).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate862).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate574).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate574).bound:ℝ) at hb
  exact (exponentialBound287 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches288 : (MergedCutGroups.Batch072.certificate864).GlobalMatches MergedCutGroups.Batch072.certificate865 CountingCertificates.Batch028.certificate576 CutLabelCertificates.Entropy014.certificate289 CutLabelCertificates.Minority014.certificate288 := by decide +kernel
theorem exponentialBound288 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate864).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate576).dm (WitnessCertificates.Batch028.certificate576).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate576).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch072.certificate864).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch072.certificate865).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate576).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch072.certificate864 MergedCutGroups.Batch072.certificate865 CountingCertificates.Batch028.certificate576 CutLabelCertificates.Entropy014.certificate289 CutLabelCertificates.Minority014.certificate288 matches288 rfl rfl
    MergedCutGroups.Batch072.numericValid864 MergedCutGroups.Batch072.numericValid865 MergedCutGroups.Batch072.cellsSound864 MergedCutGroups.Batch072.cellsSound865
    MergedCutGroups.Batch072.cellsNumeric864 MergedCutGroups.Batch072.cellsNumeric865 MergedCutGroups.Batch072.populationMatches864 MergedCutGroups.Batch072.populationMatches865
    PopulationCertificates.Batch028.valid576 PopulationCertificates.Batch028.sound576 WitnessCertificates.Batch028.valid576 WitnessCertificates.Batch028.sound576 CountingCertificates.Batch028.valid576 CountingCertificates.Batch028.sound576
    CutLabelCertificates.Entropy014.valid289 CutLabelCertificates.Minority014.valid288 CutLabelCertificates.Minority014.sound288 H st hI
theorem probabilityBound288 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate864).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate576).dm (WitnessCertificates.Batch028.certificate576).beta) ≤ ((CutFailureCertificates.Budget028.certificate576).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound576 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate576).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate864).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate865).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate576).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate576).bound:ℝ) at hb
  exact (exponentialBound288 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches289 : (MergedCutGroups.Batch072.certificate867).GlobalMatches MergedCutGroups.Batch072.certificate868 CountingCertificates.Batch028.certificate578 CutLabelCertificates.Entropy014.certificate290 CutLabelCertificates.Minority014.certificate289 := by decide +kernel
theorem exponentialBound289 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate867).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate578).dm (WitnessCertificates.Batch028.certificate578).beta) ≤ (2*exp (-((CountingCertificates.Batch028.certificate578).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch072.certificate867).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch072.certificate868).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch028.certificate578).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch072.certificate867 MergedCutGroups.Batch072.certificate868 CountingCertificates.Batch028.certificate578 CutLabelCertificates.Entropy014.certificate290 CutLabelCertificates.Minority014.certificate289 matches289 rfl rfl
    MergedCutGroups.Batch072.numericValid867 MergedCutGroups.Batch072.numericValid868 MergedCutGroups.Batch072.cellsSound867 MergedCutGroups.Batch072.cellsSound868
    MergedCutGroups.Batch072.cellsNumeric867 MergedCutGroups.Batch072.cellsNumeric868 MergedCutGroups.Batch072.populationMatches867 MergedCutGroups.Batch072.populationMatches868
    PopulationCertificates.Batch028.valid578 PopulationCertificates.Batch028.sound578 WitnessCertificates.Batch028.valid578 WitnessCertificates.Batch028.sound578 CountingCertificates.Batch028.valid578 CountingCertificates.Batch028.sound578
    CutLabelCertificates.Entropy014.valid290 CutLabelCertificates.Minority014.valid289 CutLabelCertificates.Minority014.sound289 H st hI
theorem probabilityBound289 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate867).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch028.certificate578).dm (WitnessCertificates.Batch028.certificate578).beta) ≤ ((CutFailureCertificates.Budget028.certificate578).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound578 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate578).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate867).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate868).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch028.certificate578).omega:ℝ) ≤ ((CutFailureCertificates.Budget028.certificate578).bound:ℝ) at hb
  exact (exponentialBound289 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches290 : (MergedCutGroups.Batch072.certificate870).GlobalMatches MergedCutGroups.Batch072.certificate871 CountingCertificates.Batch029.certificate580 CutLabelCertificates.Entropy014.certificate291 CutLabelCertificates.Minority014.certificate290 := by decide +kernel
theorem exponentialBound290 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate870).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate580).dm (WitnessCertificates.Batch029.certificate580).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate580).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch072.certificate870).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch072.certificate871).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate580).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch072.certificate870 MergedCutGroups.Batch072.certificate871 CountingCertificates.Batch029.certificate580 CutLabelCertificates.Entropy014.certificate291 CutLabelCertificates.Minority014.certificate290 matches290 rfl rfl
    MergedCutGroups.Batch072.numericValid870 MergedCutGroups.Batch072.numericValid871 MergedCutGroups.Batch072.cellsSound870 MergedCutGroups.Batch072.cellsSound871
    MergedCutGroups.Batch072.cellsNumeric870 MergedCutGroups.Batch072.cellsNumeric871 MergedCutGroups.Batch072.populationMatches870 MergedCutGroups.Batch072.populationMatches871
    PopulationCertificates.Batch029.valid580 PopulationCertificates.Batch029.sound580 WitnessCertificates.Batch029.valid580 WitnessCertificates.Batch029.sound580 CountingCertificates.Batch029.valid580 CountingCertificates.Batch029.sound580
    CutLabelCertificates.Entropy014.valid291 CutLabelCertificates.Minority014.valid290 CutLabelCertificates.Minority014.sound290 H st hI
theorem probabilityBound290 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate870).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate580).dm (WitnessCertificates.Batch029.certificate580).beta) ≤ ((CutFailureCertificates.Budget029.certificate580).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound580 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate580).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate870).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate871).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate580).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate580).bound:ℝ) at hb
  exact (exponentialBound290 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches291 : (MergedCutGroups.Batch072.certificate873).GlobalMatches MergedCutGroups.Batch072.certificate874 CountingCertificates.Batch029.certificate582 CutLabelCertificates.Entropy014.certificate292 CutLabelCertificates.Minority014.certificate291 := by decide +kernel
theorem exponentialBound291 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate873).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate582).dm (WitnessCertificates.Batch029.certificate582).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate582).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch072.certificate873).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch072.certificate874).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate582).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch072.certificate873 MergedCutGroups.Batch072.certificate874 CountingCertificates.Batch029.certificate582 CutLabelCertificates.Entropy014.certificate292 CutLabelCertificates.Minority014.certificate291 matches291 rfl rfl
    MergedCutGroups.Batch072.numericValid873 MergedCutGroups.Batch072.numericValid874 MergedCutGroups.Batch072.cellsSound873 MergedCutGroups.Batch072.cellsSound874
    MergedCutGroups.Batch072.cellsNumeric873 MergedCutGroups.Batch072.cellsNumeric874 MergedCutGroups.Batch072.populationMatches873 MergedCutGroups.Batch072.populationMatches874
    PopulationCertificates.Batch029.valid582 PopulationCertificates.Batch029.sound582 WitnessCertificates.Batch029.valid582 WitnessCertificates.Batch029.sound582 CountingCertificates.Batch029.valid582 CountingCertificates.Batch029.sound582
    CutLabelCertificates.Entropy014.valid292 CutLabelCertificates.Minority014.valid291 CutLabelCertificates.Minority014.sound291 H st hI
theorem probabilityBound291 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate873).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate582).dm (WitnessCertificates.Batch029.certificate582).beta) ≤ ((CutFailureCertificates.Budget029.certificate582).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound582 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate582).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate873).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate874).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate582).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate582).bound:ℝ) at hb
  exact (exponentialBound291 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches292 : (MergedCutGroups.Batch073.certificate876).GlobalMatches MergedCutGroups.Batch073.certificate877 CountingCertificates.Batch029.certificate584 CutLabelCertificates.Entropy014.certificate293 CutLabelCertificates.Minority014.certificate292 := by decide +kernel
theorem exponentialBound292 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate876).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate584).dm (WitnessCertificates.Batch029.certificate584).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate584).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch073.certificate876).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch073.certificate877).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate584).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch073.certificate876 MergedCutGroups.Batch073.certificate877 CountingCertificates.Batch029.certificate584 CutLabelCertificates.Entropy014.certificate293 CutLabelCertificates.Minority014.certificate292 matches292 rfl rfl
    MergedCutGroups.Batch073.numericValid876 MergedCutGroups.Batch073.numericValid877 MergedCutGroups.Batch073.cellsSound876 MergedCutGroups.Batch073.cellsSound877
    MergedCutGroups.Batch073.cellsNumeric876 MergedCutGroups.Batch073.cellsNumeric877 MergedCutGroups.Batch073.populationMatches876 MergedCutGroups.Batch073.populationMatches877
    PopulationCertificates.Batch029.valid584 PopulationCertificates.Batch029.sound584 WitnessCertificates.Batch029.valid584 WitnessCertificates.Batch029.sound584 CountingCertificates.Batch029.valid584 CountingCertificates.Batch029.sound584
    CutLabelCertificates.Entropy014.valid293 CutLabelCertificates.Minority014.valid292 CutLabelCertificates.Minority014.sound292 H st hI
theorem probabilityBound292 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate876).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate584).dm (WitnessCertificates.Batch029.certificate584).beta) ≤ ((CutFailureCertificates.Budget029.certificate584).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound584 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate584).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate876).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate877).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate584).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate584).bound:ℝ) at hb
  exact (exponentialBound292 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches293 : (MergedCutGroups.Batch073.certificate879).GlobalMatches MergedCutGroups.Batch073.certificate880 CountingCertificates.Batch029.certificate586 CutLabelCertificates.Entropy014.certificate294 CutLabelCertificates.Minority014.certificate293 := by decide +kernel
theorem exponentialBound293 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate879).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate586).dm (WitnessCertificates.Batch029.certificate586).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate586).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch073.certificate879).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch073.certificate880).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate586).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch073.certificate879 MergedCutGroups.Batch073.certificate880 CountingCertificates.Batch029.certificate586 CutLabelCertificates.Entropy014.certificate294 CutLabelCertificates.Minority014.certificate293 matches293 rfl rfl
    MergedCutGroups.Batch073.numericValid879 MergedCutGroups.Batch073.numericValid880 MergedCutGroups.Batch073.cellsSound879 MergedCutGroups.Batch073.cellsSound880
    MergedCutGroups.Batch073.cellsNumeric879 MergedCutGroups.Batch073.cellsNumeric880 MergedCutGroups.Batch073.populationMatches879 MergedCutGroups.Batch073.populationMatches880
    PopulationCertificates.Batch029.valid586 PopulationCertificates.Batch029.sound586 WitnessCertificates.Batch029.valid586 WitnessCertificates.Batch029.sound586 CountingCertificates.Batch029.valid586 CountingCertificates.Batch029.sound586
    CutLabelCertificates.Entropy014.valid294 CutLabelCertificates.Minority014.valid293 CutLabelCertificates.Minority014.sound293 H st hI
theorem probabilityBound293 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate879).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate586).dm (WitnessCertificates.Batch029.certificate586).beta) ≤ ((CutFailureCertificates.Budget029.certificate586).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound586 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate586).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate879).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate880).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate586).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate586).bound:ℝ) at hb
  exact (exponentialBound293 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches294 : (MergedCutGroups.Batch073.certificate882).GlobalMatches MergedCutGroups.Batch073.certificate883 CountingCertificates.Batch029.certificate588 CutLabelCertificates.Entropy014.certificate295 CutLabelCertificates.Minority014.certificate294 := by decide +kernel
theorem exponentialBound294 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate882).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate588).dm (WitnessCertificates.Batch029.certificate588).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate588).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch073.certificate882).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch073.certificate883).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate588).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch073.certificate882 MergedCutGroups.Batch073.certificate883 CountingCertificates.Batch029.certificate588 CutLabelCertificates.Entropy014.certificate295 CutLabelCertificates.Minority014.certificate294 matches294 rfl rfl
    MergedCutGroups.Batch073.numericValid882 MergedCutGroups.Batch073.numericValid883 MergedCutGroups.Batch073.cellsSound882 MergedCutGroups.Batch073.cellsSound883
    MergedCutGroups.Batch073.cellsNumeric882 MergedCutGroups.Batch073.cellsNumeric883 MergedCutGroups.Batch073.populationMatches882 MergedCutGroups.Batch073.populationMatches883
    PopulationCertificates.Batch029.valid588 PopulationCertificates.Batch029.sound588 WitnessCertificates.Batch029.valid588 WitnessCertificates.Batch029.sound588 CountingCertificates.Batch029.valid588 CountingCertificates.Batch029.sound588
    CutLabelCertificates.Entropy014.valid295 CutLabelCertificates.Minority014.valid294 CutLabelCertificates.Minority014.sound294 H st hI
theorem probabilityBound294 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate882).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate588).dm (WitnessCertificates.Batch029.certificate588).beta) ≤ ((CutFailureCertificates.Budget029.certificate588).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound588 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate588).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate882).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate883).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate588).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate588).bound:ℝ) at hb
  exact (exponentialBound294 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches295 : (MergedCutGroups.Batch073.certificate885).GlobalMatches MergedCutGroups.Batch073.certificate886 CountingCertificates.Batch029.certificate590 CutLabelCertificates.Entropy014.certificate296 CutLabelCertificates.Minority014.certificate295 := by decide +kernel
theorem exponentialBound295 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate885).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate590).dm (WitnessCertificates.Batch029.certificate590).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate590).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch073.certificate885).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch073.certificate886).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate590).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch073.certificate885 MergedCutGroups.Batch073.certificate886 CountingCertificates.Batch029.certificate590 CutLabelCertificates.Entropy014.certificate296 CutLabelCertificates.Minority014.certificate295 matches295 rfl rfl
    MergedCutGroups.Batch073.numericValid885 MergedCutGroups.Batch073.numericValid886 MergedCutGroups.Batch073.cellsSound885 MergedCutGroups.Batch073.cellsSound886
    MergedCutGroups.Batch073.cellsNumeric885 MergedCutGroups.Batch073.cellsNumeric886 MergedCutGroups.Batch073.populationMatches885 MergedCutGroups.Batch073.populationMatches886
    PopulationCertificates.Batch029.valid590 PopulationCertificates.Batch029.sound590 WitnessCertificates.Batch029.valid590 WitnessCertificates.Batch029.sound590 CountingCertificates.Batch029.valid590 CountingCertificates.Batch029.sound590
    CutLabelCertificates.Entropy014.valid296 CutLabelCertificates.Minority014.valid295 CutLabelCertificates.Minority014.sound295 H st hI
theorem probabilityBound295 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate885).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate590).dm (WitnessCertificates.Batch029.certificate590).beta) ≤ ((CutFailureCertificates.Budget029.certificate590).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound590 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate590).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate885).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate886).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate590).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate590).bound:ℝ) at hb
  exact (exponentialBound295 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches296 : (MergedCutGroups.Batch074.certificate888).GlobalMatches MergedCutGroups.Batch074.certificate889 CountingCertificates.Batch029.certificate592 CutLabelCertificates.Entropy014.certificate297 CutLabelCertificates.Minority014.certificate296 := by decide +kernel
theorem exponentialBound296 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate888).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate592).dm (WitnessCertificates.Batch029.certificate592).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate592).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch074.certificate888).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch074.certificate889).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate592).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch074.certificate888 MergedCutGroups.Batch074.certificate889 CountingCertificates.Batch029.certificate592 CutLabelCertificates.Entropy014.certificate297 CutLabelCertificates.Minority014.certificate296 matches296 rfl rfl
    MergedCutGroups.Batch074.numericValid888 MergedCutGroups.Batch074.numericValid889 MergedCutGroups.Batch074.cellsSound888 MergedCutGroups.Batch074.cellsSound889
    MergedCutGroups.Batch074.cellsNumeric888 MergedCutGroups.Batch074.cellsNumeric889 MergedCutGroups.Batch074.populationMatches888 MergedCutGroups.Batch074.populationMatches889
    PopulationCertificates.Batch029.valid592 PopulationCertificates.Batch029.sound592 WitnessCertificates.Batch029.valid592 WitnessCertificates.Batch029.sound592 CountingCertificates.Batch029.valid592 CountingCertificates.Batch029.sound592
    CutLabelCertificates.Entropy014.valid297 CutLabelCertificates.Minority014.valid296 CutLabelCertificates.Minority014.sound296 H st hI
theorem probabilityBound296 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate888).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate592).dm (WitnessCertificates.Batch029.certificate592).beta) ≤ ((CutFailureCertificates.Budget029.certificate592).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound592 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate592).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate888).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate889).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate592).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate592).bound:ℝ) at hb
  exact (exponentialBound296 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches297 : (MergedCutGroups.Batch074.certificate891).GlobalMatches MergedCutGroups.Batch074.certificate892 CountingCertificates.Batch029.certificate594 CutLabelCertificates.Entropy014.certificate298 CutLabelCertificates.Minority014.certificate297 := by decide +kernel
theorem exponentialBound297 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate891).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate594).dm (WitnessCertificates.Batch029.certificate594).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate594).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch074.certificate891).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch074.certificate892).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate594).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch074.certificate891 MergedCutGroups.Batch074.certificate892 CountingCertificates.Batch029.certificate594 CutLabelCertificates.Entropy014.certificate298 CutLabelCertificates.Minority014.certificate297 matches297 rfl rfl
    MergedCutGroups.Batch074.numericValid891 MergedCutGroups.Batch074.numericValid892 MergedCutGroups.Batch074.cellsSound891 MergedCutGroups.Batch074.cellsSound892
    MergedCutGroups.Batch074.cellsNumeric891 MergedCutGroups.Batch074.cellsNumeric892 MergedCutGroups.Batch074.populationMatches891 MergedCutGroups.Batch074.populationMatches892
    PopulationCertificates.Batch029.valid594 PopulationCertificates.Batch029.sound594 WitnessCertificates.Batch029.valid594 WitnessCertificates.Batch029.sound594 CountingCertificates.Batch029.valid594 CountingCertificates.Batch029.sound594
    CutLabelCertificates.Entropy014.valid298 CutLabelCertificates.Minority014.valid297 CutLabelCertificates.Minority014.sound297 H st hI
theorem probabilityBound297 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate891).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate594).dm (WitnessCertificates.Batch029.certificate594).beta) ≤ ((CutFailureCertificates.Budget029.certificate594).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound594 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate594).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate891).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate892).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate594).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate594).bound:ℝ) at hb
  exact (exponentialBound297 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches298 : (MergedCutGroups.Batch074.certificate894).GlobalMatches MergedCutGroups.Batch074.certificate895 CountingCertificates.Batch029.certificate596 CutLabelCertificates.Entropy014.certificate299 CutLabelCertificates.Minority014.certificate298 := by decide +kernel
theorem exponentialBound298 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate894).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate596).dm (WitnessCertificates.Batch029.certificate596).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate596).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch074.certificate894).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch074.certificate895).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate596).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch074.certificate894 MergedCutGroups.Batch074.certificate895 CountingCertificates.Batch029.certificate596 CutLabelCertificates.Entropy014.certificate299 CutLabelCertificates.Minority014.certificate298 matches298 rfl rfl
    MergedCutGroups.Batch074.numericValid894 MergedCutGroups.Batch074.numericValid895 MergedCutGroups.Batch074.cellsSound894 MergedCutGroups.Batch074.cellsSound895
    MergedCutGroups.Batch074.cellsNumeric894 MergedCutGroups.Batch074.cellsNumeric895 MergedCutGroups.Batch074.populationMatches894 MergedCutGroups.Batch074.populationMatches895
    PopulationCertificates.Batch029.valid596 PopulationCertificates.Batch029.sound596 WitnessCertificates.Batch029.valid596 WitnessCertificates.Batch029.sound596 CountingCertificates.Batch029.valid596 CountingCertificates.Batch029.sound596
    CutLabelCertificates.Entropy014.valid299 CutLabelCertificates.Minority014.valid298 CutLabelCertificates.Minority014.sound298 H st hI
theorem probabilityBound298 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate894).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate596).dm (WitnessCertificates.Batch029.certificate596).beta) ≤ ((CutFailureCertificates.Budget029.certificate596).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound596 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate596).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate894).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate895).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate596).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate596).bound:ℝ) at hb
  exact (exponentialBound298 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches299 : (MergedCutGroups.Batch074.certificate897).GlobalMatches MergedCutGroups.Batch074.certificate898 CountingCertificates.Batch029.certificate598 CutLabelCertificates.Entropy015.certificate300 CutLabelCertificates.Minority014.certificate299 := by decide +kernel
theorem exponentialBound299 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate897).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate598).dm (WitnessCertificates.Batch029.certificate598).beta) ≤ (2*exp (-((CountingCertificates.Batch029.certificate598).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch074.certificate897).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch074.certificate898).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch029.certificate598).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch074.certificate897 MergedCutGroups.Batch074.certificate898 CountingCertificates.Batch029.certificate598 CutLabelCertificates.Entropy015.certificate300 CutLabelCertificates.Minority014.certificate299 matches299 rfl rfl
    MergedCutGroups.Batch074.numericValid897 MergedCutGroups.Batch074.numericValid898 MergedCutGroups.Batch074.cellsSound897 MergedCutGroups.Batch074.cellsSound898
    MergedCutGroups.Batch074.cellsNumeric897 MergedCutGroups.Batch074.cellsNumeric898 MergedCutGroups.Batch074.populationMatches897 MergedCutGroups.Batch074.populationMatches898
    PopulationCertificates.Batch029.valid598 PopulationCertificates.Batch029.sound598 WitnessCertificates.Batch029.valid598 WitnessCertificates.Batch029.sound598 CountingCertificates.Batch029.valid598 CountingCertificates.Batch029.sound598
    CutLabelCertificates.Entropy015.valid300 CutLabelCertificates.Minority014.valid299 CutLabelCertificates.Minority014.sound299 H st hI
theorem probabilityBound299 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate897).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch029.certificate598).dm (WitnessCertificates.Batch029.certificate598).beta) ≤ ((CutFailureCertificates.Budget029.certificate598).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound598 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate598).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate897).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate898).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch029.certificate598).omega:ℝ) ≤ ((CutFailureCertificates.Budget029.certificate598).bound:ℝ) at hb
  exact (exponentialBound299 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch014
