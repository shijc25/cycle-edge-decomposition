import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch004
import Cycle12.CountingCertificates.Batch005
import Cycle12.CutFailureCertificates.Budget004
import Cycle12.CutFailureCertificates.Budget005
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

namespace Cycle12.CertifiedAnchorFailures.Batch002
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches40 : (MergedCutGroups.Batch010.certificate122).AnchorMatches CountingCertificates.Batch004.certificate81 := by decide +kernel
theorem exponentialBound40 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate122).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate81).dm (WitnessCertificates.Batch004.certificate81).beta (WitnessCertificates.Batch004.certificate81).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate81).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch010.certificate122).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate81).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch010.certificate122 CountingCertificates.Batch004.certificate81 matches40 MergedCutGroups.Batch010.numericValid122 MergedCutGroups.Batch010.cellsSound122 MergedCutGroups.Batch010.cellsNumeric122 MergedCutGroups.Batch010.populationMatches122
    PopulationCertificates.Batch004.valid81 PopulationCertificates.Batch004.sound81 WitnessCertificates.Batch004.valid81 WitnessCertificates.Batch004.sound81 CountingCertificates.Batch004.valid81 CountingCertificates.Batch004.sound81 H st hI
theorem probabilityBound40 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate122).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate81).dm (WitnessCertificates.Batch004.certificate81).beta (WitnessCertificates.Batch004.certificate81).L) ≤ ((CutFailureCertificates.Budget004.certificate81).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound81 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate81).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate122).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate81).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate81).bound:ℝ) at hb
  exact (exponentialBound40 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches41 : (MergedCutGroups.Batch010.certificate125).AnchorMatches CountingCertificates.Batch004.certificate83 := by decide +kernel
theorem exponentialBound41 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate125).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate83).dm (WitnessCertificates.Batch004.certificate83).beta (WitnessCertificates.Batch004.certificate83).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate83).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch010.certificate125).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate83).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch010.certificate125 CountingCertificates.Batch004.certificate83 matches41 MergedCutGroups.Batch010.numericValid125 MergedCutGroups.Batch010.cellsSound125 MergedCutGroups.Batch010.cellsNumeric125 MergedCutGroups.Batch010.populationMatches125
    PopulationCertificates.Batch004.valid83 PopulationCertificates.Batch004.sound83 WitnessCertificates.Batch004.valid83 WitnessCertificates.Batch004.sound83 CountingCertificates.Batch004.valid83 CountingCertificates.Batch004.sound83 H st hI
theorem probabilityBound41 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate125).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate83).dm (WitnessCertificates.Batch004.certificate83).beta (WitnessCertificates.Batch004.certificate83).L) ≤ ((CutFailureCertificates.Budget004.certificate83).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound83 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate83).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate125).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate83).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate83).bound:ℝ) at hb
  exact (exponentialBound41 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches42 : (MergedCutGroups.Batch010.certificate128).AnchorMatches CountingCertificates.Batch004.certificate85 := by decide +kernel
theorem exponentialBound42 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate128).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate85).dm (WitnessCertificates.Batch004.certificate85).beta (WitnessCertificates.Batch004.certificate85).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate85).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch010.certificate128).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate85).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch010.certificate128 CountingCertificates.Batch004.certificate85 matches42 MergedCutGroups.Batch010.numericValid128 MergedCutGroups.Batch010.cellsSound128 MergedCutGroups.Batch010.cellsNumeric128 MergedCutGroups.Batch010.populationMatches128
    PopulationCertificates.Batch004.valid85 PopulationCertificates.Batch004.sound85 WitnessCertificates.Batch004.valid85 WitnessCertificates.Batch004.sound85 CountingCertificates.Batch004.valid85 CountingCertificates.Batch004.sound85 H st hI
theorem probabilityBound42 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate128).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate85).dm (WitnessCertificates.Batch004.certificate85).beta (WitnessCertificates.Batch004.certificate85).L) ≤ ((CutFailureCertificates.Budget004.certificate85).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound85 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate85).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate128).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate85).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate85).bound:ℝ) at hb
  exact (exponentialBound42 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches43 : (MergedCutGroups.Batch010.certificate131).AnchorMatches CountingCertificates.Batch004.certificate87 := by decide +kernel
theorem exponentialBound43 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate131).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate87).dm (WitnessCertificates.Batch004.certificate87).beta (WitnessCertificates.Batch004.certificate87).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate87).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch010.certificate131).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate87).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch010.certificate131 CountingCertificates.Batch004.certificate87 matches43 MergedCutGroups.Batch010.numericValid131 MergedCutGroups.Batch010.cellsSound131 MergedCutGroups.Batch010.cellsNumeric131 MergedCutGroups.Batch010.populationMatches131
    PopulationCertificates.Batch004.valid87 PopulationCertificates.Batch004.sound87 WitnessCertificates.Batch004.valid87 WitnessCertificates.Batch004.sound87 CountingCertificates.Batch004.valid87 CountingCertificates.Batch004.sound87 H st hI
theorem probabilityBound43 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch010.certificate131).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate87).dm (WitnessCertificates.Batch004.certificate87).beta (WitnessCertificates.Batch004.certificate87).L) ≤ ((CutFailureCertificates.Budget004.certificate87).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound87 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate87).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch010.certificate131).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate87).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate87).bound:ℝ) at hb
  exact (exponentialBound43 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches44 : (MergedCutGroups.Batch011.certificate134).AnchorMatches CountingCertificates.Batch004.certificate89 := by decide +kernel
theorem exponentialBound44 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate134).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate89).dm (WitnessCertificates.Batch004.certificate89).beta (WitnessCertificates.Batch004.certificate89).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate89).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch011.certificate134).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate89).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch011.certificate134 CountingCertificates.Batch004.certificate89 matches44 MergedCutGroups.Batch011.numericValid134 MergedCutGroups.Batch011.cellsSound134 MergedCutGroups.Batch011.cellsNumeric134 MergedCutGroups.Batch011.populationMatches134
    PopulationCertificates.Batch004.valid89 PopulationCertificates.Batch004.sound89 WitnessCertificates.Batch004.valid89 WitnessCertificates.Batch004.sound89 CountingCertificates.Batch004.valid89 CountingCertificates.Batch004.sound89 H st hI
theorem probabilityBound44 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate134).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate89).dm (WitnessCertificates.Batch004.certificate89).beta (WitnessCertificates.Batch004.certificate89).L) ≤ ((CutFailureCertificates.Budget004.certificate89).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound89 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate89).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate134).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate89).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate89).bound:ℝ) at hb
  exact (exponentialBound44 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches45 : (MergedCutGroups.Batch011.certificate137).AnchorMatches CountingCertificates.Batch004.certificate91 := by decide +kernel
theorem exponentialBound45 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate137).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate91).dm (WitnessCertificates.Batch004.certificate91).beta (WitnessCertificates.Batch004.certificate91).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate91).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch011.certificate137).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate91).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch011.certificate137 CountingCertificates.Batch004.certificate91 matches45 MergedCutGroups.Batch011.numericValid137 MergedCutGroups.Batch011.cellsSound137 MergedCutGroups.Batch011.cellsNumeric137 MergedCutGroups.Batch011.populationMatches137
    PopulationCertificates.Batch004.valid91 PopulationCertificates.Batch004.sound91 WitnessCertificates.Batch004.valid91 WitnessCertificates.Batch004.sound91 CountingCertificates.Batch004.valid91 CountingCertificates.Batch004.sound91 H st hI
theorem probabilityBound45 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate137).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate91).dm (WitnessCertificates.Batch004.certificate91).beta (WitnessCertificates.Batch004.certificate91).L) ≤ ((CutFailureCertificates.Budget004.certificate91).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound91 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate91).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate137).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate91).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate91).bound:ℝ) at hb
  exact (exponentialBound45 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches46 : (MergedCutGroups.Batch011.certificate140).AnchorMatches CountingCertificates.Batch004.certificate93 := by decide +kernel
theorem exponentialBound46 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate140).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate93).dm (WitnessCertificates.Batch004.certificate93).beta (WitnessCertificates.Batch004.certificate93).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate93).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch011.certificate140).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate93).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch011.certificate140 CountingCertificates.Batch004.certificate93 matches46 MergedCutGroups.Batch011.numericValid140 MergedCutGroups.Batch011.cellsSound140 MergedCutGroups.Batch011.cellsNumeric140 MergedCutGroups.Batch011.populationMatches140
    PopulationCertificates.Batch004.valid93 PopulationCertificates.Batch004.sound93 WitnessCertificates.Batch004.valid93 WitnessCertificates.Batch004.sound93 CountingCertificates.Batch004.valid93 CountingCertificates.Batch004.sound93 H st hI
theorem probabilityBound46 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate140).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate93).dm (WitnessCertificates.Batch004.certificate93).beta (WitnessCertificates.Batch004.certificate93).L) ≤ ((CutFailureCertificates.Budget004.certificate93).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound93 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate93).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate140).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate93).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate93).bound:ℝ) at hb
  exact (exponentialBound46 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches47 : (MergedCutGroups.Batch011.certificate143).AnchorMatches CountingCertificates.Batch004.certificate95 := by decide +kernel
theorem exponentialBound47 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate143).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate95).dm (WitnessCertificates.Batch004.certificate95).beta (WitnessCertificates.Batch004.certificate95).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate95).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch011.certificate143).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate95).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch011.certificate143 CountingCertificates.Batch004.certificate95 matches47 MergedCutGroups.Batch011.numericValid143 MergedCutGroups.Batch011.cellsSound143 MergedCutGroups.Batch011.cellsNumeric143 MergedCutGroups.Batch011.populationMatches143
    PopulationCertificates.Batch004.valid95 PopulationCertificates.Batch004.sound95 WitnessCertificates.Batch004.valid95 WitnessCertificates.Batch004.sound95 CountingCertificates.Batch004.valid95 CountingCertificates.Batch004.sound95 H st hI
theorem probabilityBound47 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch011.certificate143).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate95).dm (WitnessCertificates.Batch004.certificate95).beta (WitnessCertificates.Batch004.certificate95).L) ≤ ((CutFailureCertificates.Budget004.certificate95).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound95 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate95).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch011.certificate143).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate95).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate95).bound:ℝ) at hb
  exact (exponentialBound47 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches48 : (MergedCutGroups.Batch012.certificate146).AnchorMatches CountingCertificates.Batch004.certificate97 := by decide +kernel
theorem exponentialBound48 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate146).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate97).dm (WitnessCertificates.Batch004.certificate97).beta (WitnessCertificates.Batch004.certificate97).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate97).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch012.certificate146).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate97).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch012.certificate146 CountingCertificates.Batch004.certificate97 matches48 MergedCutGroups.Batch012.numericValid146 MergedCutGroups.Batch012.cellsSound146 MergedCutGroups.Batch012.cellsNumeric146 MergedCutGroups.Batch012.populationMatches146
    PopulationCertificates.Batch004.valid97 PopulationCertificates.Batch004.sound97 WitnessCertificates.Batch004.valid97 WitnessCertificates.Batch004.sound97 CountingCertificates.Batch004.valid97 CountingCertificates.Batch004.sound97 H st hI
theorem probabilityBound48 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate146).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate97).dm (WitnessCertificates.Batch004.certificate97).beta (WitnessCertificates.Batch004.certificate97).L) ≤ ((CutFailureCertificates.Budget004.certificate97).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound97 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate97).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate146).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate97).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate97).bound:ℝ) at hb
  exact (exponentialBound48 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches49 : (MergedCutGroups.Batch012.certificate149).AnchorMatches CountingCertificates.Batch004.certificate99 := by decide +kernel
theorem exponentialBound49 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate149).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate99).dm (WitnessCertificates.Batch004.certificate99).beta (WitnessCertificates.Batch004.certificate99).L) ≤ (2*exp (-((CountingCertificates.Batch004.certificate99).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch012.certificate149).exponent:ℝ)*st.R))/((WitnessCertificates.Batch004.certificate99).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch012.certificate149 CountingCertificates.Batch004.certificate99 matches49 MergedCutGroups.Batch012.numericValid149 MergedCutGroups.Batch012.cellsSound149 MergedCutGroups.Batch012.cellsNumeric149 MergedCutGroups.Batch012.populationMatches149
    PopulationCertificates.Batch004.valid99 PopulationCertificates.Batch004.sound99 WitnessCertificates.Batch004.valid99 WitnessCertificates.Batch004.sound99 CountingCertificates.Batch004.valid99 CountingCertificates.Batch004.sound99 H st hI
theorem probabilityBound49 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate149).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch004.certificate99).dm (WitnessCertificates.Batch004.certificate99).beta (WitnessCertificates.Batch004.certificate99).L) ≤ ((CutFailureCertificates.Budget004.certificate99).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget004.sound99 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch004.certificate99).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate149).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch004.certificate99).omega:ℝ)) ≤ ((CutFailureCertificates.Budget004.certificate99).bound:ℝ) at hb
  exact (exponentialBound49 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches50 : (MergedCutGroups.Batch012.certificate152).AnchorMatches CountingCertificates.Batch005.certificate101 := by decide +kernel
theorem exponentialBound50 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate152).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate101).dm (WitnessCertificates.Batch005.certificate101).beta (WitnessCertificates.Batch005.certificate101).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate101).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch012.certificate152).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate101).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch012.certificate152 CountingCertificates.Batch005.certificate101 matches50 MergedCutGroups.Batch012.numericValid152 MergedCutGroups.Batch012.cellsSound152 MergedCutGroups.Batch012.cellsNumeric152 MergedCutGroups.Batch012.populationMatches152
    PopulationCertificates.Batch005.valid101 PopulationCertificates.Batch005.sound101 WitnessCertificates.Batch005.valid101 WitnessCertificates.Batch005.sound101 CountingCertificates.Batch005.valid101 CountingCertificates.Batch005.sound101 H st hI
theorem probabilityBound50 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate152).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate101).dm (WitnessCertificates.Batch005.certificate101).beta (WitnessCertificates.Batch005.certificate101).L) ≤ ((CutFailureCertificates.Budget005.certificate101).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound101 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate101).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate152).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate101).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate101).bound:ℝ) at hb
  exact (exponentialBound50 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches51 : (MergedCutGroups.Batch012.certificate155).AnchorMatches CountingCertificates.Batch005.certificate103 := by decide +kernel
theorem exponentialBound51 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate155).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate103).dm (WitnessCertificates.Batch005.certificate103).beta (WitnessCertificates.Batch005.certificate103).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate103).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch012.certificate155).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate103).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch012.certificate155 CountingCertificates.Batch005.certificate103 matches51 MergedCutGroups.Batch012.numericValid155 MergedCutGroups.Batch012.cellsSound155 MergedCutGroups.Batch012.cellsNumeric155 MergedCutGroups.Batch012.populationMatches155
    PopulationCertificates.Batch005.valid103 PopulationCertificates.Batch005.sound103 WitnessCertificates.Batch005.valid103 WitnessCertificates.Batch005.sound103 CountingCertificates.Batch005.valid103 CountingCertificates.Batch005.sound103 H st hI
theorem probabilityBound51 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch012.certificate155).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate103).dm (WitnessCertificates.Batch005.certificate103).beta (WitnessCertificates.Batch005.certificate103).L) ≤ ((CutFailureCertificates.Budget005.certificate103).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound103 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate103).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch012.certificate155).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate103).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate103).bound:ℝ) at hb
  exact (exponentialBound51 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches52 : (MergedCutGroups.Batch013.certificate158).AnchorMatches CountingCertificates.Batch005.certificate105 := by decide +kernel
theorem exponentialBound52 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate158).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate105).dm (WitnessCertificates.Batch005.certificate105).beta (WitnessCertificates.Batch005.certificate105).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate105).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch013.certificate158).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate105).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch013.certificate158 CountingCertificates.Batch005.certificate105 matches52 MergedCutGroups.Batch013.numericValid158 MergedCutGroups.Batch013.cellsSound158 MergedCutGroups.Batch013.cellsNumeric158 MergedCutGroups.Batch013.populationMatches158
    PopulationCertificates.Batch005.valid105 PopulationCertificates.Batch005.sound105 WitnessCertificates.Batch005.valid105 WitnessCertificates.Batch005.sound105 CountingCertificates.Batch005.valid105 CountingCertificates.Batch005.sound105 H st hI
theorem probabilityBound52 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate158).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate105).dm (WitnessCertificates.Batch005.certificate105).beta (WitnessCertificates.Batch005.certificate105).L) ≤ ((CutFailureCertificates.Budget005.certificate105).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound105 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate105).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate158).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate105).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate105).bound:ℝ) at hb
  exact (exponentialBound52 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches53 : (MergedCutGroups.Batch013.certificate161).AnchorMatches CountingCertificates.Batch005.certificate107 := by decide +kernel
theorem exponentialBound53 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate161).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate107).dm (WitnessCertificates.Batch005.certificate107).beta (WitnessCertificates.Batch005.certificate107).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate107).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch013.certificate161).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate107).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch013.certificate161 CountingCertificates.Batch005.certificate107 matches53 MergedCutGroups.Batch013.numericValid161 MergedCutGroups.Batch013.cellsSound161 MergedCutGroups.Batch013.cellsNumeric161 MergedCutGroups.Batch013.populationMatches161
    PopulationCertificates.Batch005.valid107 PopulationCertificates.Batch005.sound107 WitnessCertificates.Batch005.valid107 WitnessCertificates.Batch005.sound107 CountingCertificates.Batch005.valid107 CountingCertificates.Batch005.sound107 H st hI
theorem probabilityBound53 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate161).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate107).dm (WitnessCertificates.Batch005.certificate107).beta (WitnessCertificates.Batch005.certificate107).L) ≤ ((CutFailureCertificates.Budget005.certificate107).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound107 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate107).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate161).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate107).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate107).bound:ℝ) at hb
  exact (exponentialBound53 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches54 : (MergedCutGroups.Batch013.certificate164).AnchorMatches CountingCertificates.Batch005.certificate109 := by decide +kernel
theorem exponentialBound54 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate164).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate109).dm (WitnessCertificates.Batch005.certificate109).beta (WitnessCertificates.Batch005.certificate109).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate109).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch013.certificate164).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate109).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch013.certificate164 CountingCertificates.Batch005.certificate109 matches54 MergedCutGroups.Batch013.numericValid164 MergedCutGroups.Batch013.cellsSound164 MergedCutGroups.Batch013.cellsNumeric164 MergedCutGroups.Batch013.populationMatches164
    PopulationCertificates.Batch005.valid109 PopulationCertificates.Batch005.sound109 WitnessCertificates.Batch005.valid109 WitnessCertificates.Batch005.sound109 CountingCertificates.Batch005.valid109 CountingCertificates.Batch005.sound109 H st hI
theorem probabilityBound54 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate164).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate109).dm (WitnessCertificates.Batch005.certificate109).beta (WitnessCertificates.Batch005.certificate109).L) ≤ ((CutFailureCertificates.Budget005.certificate109).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound109 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate109).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate164).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate109).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate109).bound:ℝ) at hb
  exact (exponentialBound54 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches55 : (MergedCutGroups.Batch013.certificate167).AnchorMatches CountingCertificates.Batch005.certificate111 := by decide +kernel
theorem exponentialBound55 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate167).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate111).dm (WitnessCertificates.Batch005.certificate111).beta (WitnessCertificates.Batch005.certificate111).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate111).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch013.certificate167).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate111).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch013.certificate167 CountingCertificates.Batch005.certificate111 matches55 MergedCutGroups.Batch013.numericValid167 MergedCutGroups.Batch013.cellsSound167 MergedCutGroups.Batch013.cellsNumeric167 MergedCutGroups.Batch013.populationMatches167
    PopulationCertificates.Batch005.valid111 PopulationCertificates.Batch005.sound111 WitnessCertificates.Batch005.valid111 WitnessCertificates.Batch005.sound111 CountingCertificates.Batch005.valid111 CountingCertificates.Batch005.sound111 H st hI
theorem probabilityBound55 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch013.certificate167).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate111).dm (WitnessCertificates.Batch005.certificate111).beta (WitnessCertificates.Batch005.certificate111).L) ≤ ((CutFailureCertificates.Budget005.certificate111).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound111 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate111).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch013.certificate167).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate111).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate111).bound:ℝ) at hb
  exact (exponentialBound55 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches56 : (MergedCutGroups.Batch014.certificate170).AnchorMatches CountingCertificates.Batch005.certificate113 := by decide +kernel
theorem exponentialBound56 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate170).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate113).dm (WitnessCertificates.Batch005.certificate113).beta (WitnessCertificates.Batch005.certificate113).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate113).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch014.certificate170).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate113).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch014.certificate170 CountingCertificates.Batch005.certificate113 matches56 MergedCutGroups.Batch014.numericValid170 MergedCutGroups.Batch014.cellsSound170 MergedCutGroups.Batch014.cellsNumeric170 MergedCutGroups.Batch014.populationMatches170
    PopulationCertificates.Batch005.valid113 PopulationCertificates.Batch005.sound113 WitnessCertificates.Batch005.valid113 WitnessCertificates.Batch005.sound113 CountingCertificates.Batch005.valid113 CountingCertificates.Batch005.sound113 H st hI
theorem probabilityBound56 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate170).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate113).dm (WitnessCertificates.Batch005.certificate113).beta (WitnessCertificates.Batch005.certificate113).L) ≤ ((CutFailureCertificates.Budget005.certificate113).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound113 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate113).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate170).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate113).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate113).bound:ℝ) at hb
  exact (exponentialBound56 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches57 : (MergedCutGroups.Batch014.certificate173).AnchorMatches CountingCertificates.Batch005.certificate115 := by decide +kernel
theorem exponentialBound57 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate173).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate115).dm (WitnessCertificates.Batch005.certificate115).beta (WitnessCertificates.Batch005.certificate115).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate115).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch014.certificate173).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate115).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch014.certificate173 CountingCertificates.Batch005.certificate115 matches57 MergedCutGroups.Batch014.numericValid173 MergedCutGroups.Batch014.cellsSound173 MergedCutGroups.Batch014.cellsNumeric173 MergedCutGroups.Batch014.populationMatches173
    PopulationCertificates.Batch005.valid115 PopulationCertificates.Batch005.sound115 WitnessCertificates.Batch005.valid115 WitnessCertificates.Batch005.sound115 CountingCertificates.Batch005.valid115 CountingCertificates.Batch005.sound115 H st hI
theorem probabilityBound57 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate173).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate115).dm (WitnessCertificates.Batch005.certificate115).beta (WitnessCertificates.Batch005.certificate115).L) ≤ ((CutFailureCertificates.Budget005.certificate115).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound115 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate115).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate173).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate115).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate115).bound:ℝ) at hb
  exact (exponentialBound57 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches58 : (MergedCutGroups.Batch014.certificate176).AnchorMatches CountingCertificates.Batch005.certificate117 := by decide +kernel
theorem exponentialBound58 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate176).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate117).dm (WitnessCertificates.Batch005.certificate117).beta (WitnessCertificates.Batch005.certificate117).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate117).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch014.certificate176).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate117).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch014.certificate176 CountingCertificates.Batch005.certificate117 matches58 MergedCutGroups.Batch014.numericValid176 MergedCutGroups.Batch014.cellsSound176 MergedCutGroups.Batch014.cellsNumeric176 MergedCutGroups.Batch014.populationMatches176
    PopulationCertificates.Batch005.valid117 PopulationCertificates.Batch005.sound117 WitnessCertificates.Batch005.valid117 WitnessCertificates.Batch005.sound117 CountingCertificates.Batch005.valid117 CountingCertificates.Batch005.sound117 H st hI
theorem probabilityBound58 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate176).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate117).dm (WitnessCertificates.Batch005.certificate117).beta (WitnessCertificates.Batch005.certificate117).L) ≤ ((CutFailureCertificates.Budget005.certificate117).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound117 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate117).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate176).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate117).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate117).bound:ℝ) at hb
  exact (exponentialBound58 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches59 : (MergedCutGroups.Batch014.certificate179).AnchorMatches CountingCertificates.Batch005.certificate119 := by decide +kernel
theorem exponentialBound59 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate179).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate119).dm (WitnessCertificates.Batch005.certificate119).beta (WitnessCertificates.Batch005.certificate119).L) ≤ (2*exp (-((CountingCertificates.Batch005.certificate119).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch014.certificate179).exponent:ℝ)*st.R))/((WitnessCertificates.Batch005.certificate119).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch014.certificate179 CountingCertificates.Batch005.certificate119 matches59 MergedCutGroups.Batch014.numericValid179 MergedCutGroups.Batch014.cellsSound179 MergedCutGroups.Batch014.cellsNumeric179 MergedCutGroups.Batch014.populationMatches179
    PopulationCertificates.Batch005.valid119 PopulationCertificates.Batch005.sound119 WitnessCertificates.Batch005.valid119 WitnessCertificates.Batch005.sound119 CountingCertificates.Batch005.valid119 CountingCertificates.Batch005.sound119 H st hI
theorem probabilityBound59 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch014.certificate179).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch005.certificate119).dm (WitnessCertificates.Batch005.certificate119).beta (WitnessCertificates.Batch005.certificate119).L) ≤ ((CutFailureCertificates.Budget005.certificate119).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget005.sound119 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch005.certificate119).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch014.certificate179).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch005.certificate119).omega:ℝ)) ≤ ((CutFailureCertificates.Budget005.certificate119).bound:ℝ) at hb
  exact (exponentialBound59 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch002
