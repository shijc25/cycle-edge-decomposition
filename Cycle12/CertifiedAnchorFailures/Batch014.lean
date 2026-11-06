import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch028
import Cycle12.CountingCertificates.Batch029
import Cycle12.CutFailureCertificates.Budget028
import Cycle12.CutFailureCertificates.Budget029
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

namespace Cycle12.CertifiedAnchorFailures.Batch014
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches280 : (MergedCutGroups.Batch070.certificate842).AnchorMatches CountingCertificates.Batch028.certificate561 := by decide +kernel
theorem exponentialBound280 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate842).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate561).dm (WitnessCertificates.Batch028.certificate561).beta (WitnessCertificates.Batch028.certificate561).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate561).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch070.certificate842).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate561).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch070.certificate842 CountingCertificates.Batch028.certificate561 matches280 MergedCutGroups.Batch070.numericValid842 MergedCutGroups.Batch070.cellsSound842 MergedCutGroups.Batch070.cellsNumeric842 MergedCutGroups.Batch070.populationMatches842
    PopulationCertificates.Batch028.valid561 PopulationCertificates.Batch028.sound561 WitnessCertificates.Batch028.valid561 WitnessCertificates.Batch028.sound561 CountingCertificates.Batch028.valid561 CountingCertificates.Batch028.sound561 H st hI
theorem probabilityBound280 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate842).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate561).dm (WitnessCertificates.Batch028.certificate561).beta (WitnessCertificates.Batch028.certificate561).L) ≤ ((CutFailureCertificates.Budget028.certificate561).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound561 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate561).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate842).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate561).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate561).bound:ℝ) at hb
  exact (exponentialBound280 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches281 : (MergedCutGroups.Batch070.certificate845).AnchorMatches CountingCertificates.Batch028.certificate563 := by decide +kernel
theorem exponentialBound281 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate845).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate563).dm (WitnessCertificates.Batch028.certificate563).beta (WitnessCertificates.Batch028.certificate563).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate563).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch070.certificate845).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate563).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch070.certificate845 CountingCertificates.Batch028.certificate563 matches281 MergedCutGroups.Batch070.numericValid845 MergedCutGroups.Batch070.cellsSound845 MergedCutGroups.Batch070.cellsNumeric845 MergedCutGroups.Batch070.populationMatches845
    PopulationCertificates.Batch028.valid563 PopulationCertificates.Batch028.sound563 WitnessCertificates.Batch028.valid563 WitnessCertificates.Batch028.sound563 CountingCertificates.Batch028.valid563 CountingCertificates.Batch028.sound563 H st hI
theorem probabilityBound281 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate845).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate563).dm (WitnessCertificates.Batch028.certificate563).beta (WitnessCertificates.Batch028.certificate563).L) ≤ ((CutFailureCertificates.Budget028.certificate563).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound563 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate563).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate845).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate563).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate563).bound:ℝ) at hb
  exact (exponentialBound281 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches282 : (MergedCutGroups.Batch070.certificate848).AnchorMatches CountingCertificates.Batch028.certificate565 := by decide +kernel
theorem exponentialBound282 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate848).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate565).dm (WitnessCertificates.Batch028.certificate565).beta (WitnessCertificates.Batch028.certificate565).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate565).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch070.certificate848).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate565).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch070.certificate848 CountingCertificates.Batch028.certificate565 matches282 MergedCutGroups.Batch070.numericValid848 MergedCutGroups.Batch070.cellsSound848 MergedCutGroups.Batch070.cellsNumeric848 MergedCutGroups.Batch070.populationMatches848
    PopulationCertificates.Batch028.valid565 PopulationCertificates.Batch028.sound565 WitnessCertificates.Batch028.valid565 WitnessCertificates.Batch028.sound565 CountingCertificates.Batch028.valid565 CountingCertificates.Batch028.sound565 H st hI
theorem probabilityBound282 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate848).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate565).dm (WitnessCertificates.Batch028.certificate565).beta (WitnessCertificates.Batch028.certificate565).L) ≤ ((CutFailureCertificates.Budget028.certificate565).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound565 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate565).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate848).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate565).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate565).bound:ℝ) at hb
  exact (exponentialBound282 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches283 : (MergedCutGroups.Batch070.certificate851).AnchorMatches CountingCertificates.Batch028.certificate567 := by decide +kernel
theorem exponentialBound283 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate851).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate567).dm (WitnessCertificates.Batch028.certificate567).beta (WitnessCertificates.Batch028.certificate567).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate567).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch070.certificate851).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate567).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch070.certificate851 CountingCertificates.Batch028.certificate567 matches283 MergedCutGroups.Batch070.numericValid851 MergedCutGroups.Batch070.cellsSound851 MergedCutGroups.Batch070.cellsNumeric851 MergedCutGroups.Batch070.populationMatches851
    PopulationCertificates.Batch028.valid567 PopulationCertificates.Batch028.sound567 WitnessCertificates.Batch028.valid567 WitnessCertificates.Batch028.sound567 CountingCertificates.Batch028.valid567 CountingCertificates.Batch028.sound567 H st hI
theorem probabilityBound283 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch070.certificate851).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate567).dm (WitnessCertificates.Batch028.certificate567).beta (WitnessCertificates.Batch028.certificate567).L) ≤ ((CutFailureCertificates.Budget028.certificate567).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound567 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate567).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch070.certificate851).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate567).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate567).bound:ℝ) at hb
  exact (exponentialBound283 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches284 : (MergedCutGroups.Batch071.certificate854).AnchorMatches CountingCertificates.Batch028.certificate569 := by decide +kernel
theorem exponentialBound284 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate854).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate569).dm (WitnessCertificates.Batch028.certificate569).beta (WitnessCertificates.Batch028.certificate569).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate569).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch071.certificate854).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate569).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch071.certificate854 CountingCertificates.Batch028.certificate569 matches284 MergedCutGroups.Batch071.numericValid854 MergedCutGroups.Batch071.cellsSound854 MergedCutGroups.Batch071.cellsNumeric854 MergedCutGroups.Batch071.populationMatches854
    PopulationCertificates.Batch028.valid569 PopulationCertificates.Batch028.sound569 WitnessCertificates.Batch028.valid569 WitnessCertificates.Batch028.sound569 CountingCertificates.Batch028.valid569 CountingCertificates.Batch028.sound569 H st hI
theorem probabilityBound284 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate854).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate569).dm (WitnessCertificates.Batch028.certificate569).beta (WitnessCertificates.Batch028.certificate569).L) ≤ ((CutFailureCertificates.Budget028.certificate569).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound569 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate569).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate854).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate569).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate569).bound:ℝ) at hb
  exact (exponentialBound284 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches285 : (MergedCutGroups.Batch071.certificate857).AnchorMatches CountingCertificates.Batch028.certificate571 := by decide +kernel
theorem exponentialBound285 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate857).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate571).dm (WitnessCertificates.Batch028.certificate571).beta (WitnessCertificates.Batch028.certificate571).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate571).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch071.certificate857).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate571).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch071.certificate857 CountingCertificates.Batch028.certificate571 matches285 MergedCutGroups.Batch071.numericValid857 MergedCutGroups.Batch071.cellsSound857 MergedCutGroups.Batch071.cellsNumeric857 MergedCutGroups.Batch071.populationMatches857
    PopulationCertificates.Batch028.valid571 PopulationCertificates.Batch028.sound571 WitnessCertificates.Batch028.valid571 WitnessCertificates.Batch028.sound571 CountingCertificates.Batch028.valid571 CountingCertificates.Batch028.sound571 H st hI
theorem probabilityBound285 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate857).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate571).dm (WitnessCertificates.Batch028.certificate571).beta (WitnessCertificates.Batch028.certificate571).L) ≤ ((CutFailureCertificates.Budget028.certificate571).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound571 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate571).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate857).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate571).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate571).bound:ℝ) at hb
  exact (exponentialBound285 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches286 : (MergedCutGroups.Batch071.certificate860).AnchorMatches CountingCertificates.Batch028.certificate573 := by decide +kernel
theorem exponentialBound286 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate860).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate573).dm (WitnessCertificates.Batch028.certificate573).beta (WitnessCertificates.Batch028.certificate573).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate573).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch071.certificate860).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate573).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch071.certificate860 CountingCertificates.Batch028.certificate573 matches286 MergedCutGroups.Batch071.numericValid860 MergedCutGroups.Batch071.cellsSound860 MergedCutGroups.Batch071.cellsNumeric860 MergedCutGroups.Batch071.populationMatches860
    PopulationCertificates.Batch028.valid573 PopulationCertificates.Batch028.sound573 WitnessCertificates.Batch028.valid573 WitnessCertificates.Batch028.sound573 CountingCertificates.Batch028.valid573 CountingCertificates.Batch028.sound573 H st hI
theorem probabilityBound286 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate860).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate573).dm (WitnessCertificates.Batch028.certificate573).beta (WitnessCertificates.Batch028.certificate573).L) ≤ ((CutFailureCertificates.Budget028.certificate573).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound573 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate573).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate860).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate573).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate573).bound:ℝ) at hb
  exact (exponentialBound286 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches287 : (MergedCutGroups.Batch071.certificate863).AnchorMatches CountingCertificates.Batch028.certificate575 := by decide +kernel
theorem exponentialBound287 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate863).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate575).dm (WitnessCertificates.Batch028.certificate575).beta (WitnessCertificates.Batch028.certificate575).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate575).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch071.certificate863).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate575).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch071.certificate863 CountingCertificates.Batch028.certificate575 matches287 MergedCutGroups.Batch071.numericValid863 MergedCutGroups.Batch071.cellsSound863 MergedCutGroups.Batch071.cellsNumeric863 MergedCutGroups.Batch071.populationMatches863
    PopulationCertificates.Batch028.valid575 PopulationCertificates.Batch028.sound575 WitnessCertificates.Batch028.valid575 WitnessCertificates.Batch028.sound575 CountingCertificates.Batch028.valid575 CountingCertificates.Batch028.sound575 H st hI
theorem probabilityBound287 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch071.certificate863).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate575).dm (WitnessCertificates.Batch028.certificate575).beta (WitnessCertificates.Batch028.certificate575).L) ≤ ((CutFailureCertificates.Budget028.certificate575).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound575 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate575).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch071.certificate863).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate575).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate575).bound:ℝ) at hb
  exact (exponentialBound287 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches288 : (MergedCutGroups.Batch072.certificate866).AnchorMatches CountingCertificates.Batch028.certificate577 := by decide +kernel
theorem exponentialBound288 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate866).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate577).dm (WitnessCertificates.Batch028.certificate577).beta (WitnessCertificates.Batch028.certificate577).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate577).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch072.certificate866).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate577).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch072.certificate866 CountingCertificates.Batch028.certificate577 matches288 MergedCutGroups.Batch072.numericValid866 MergedCutGroups.Batch072.cellsSound866 MergedCutGroups.Batch072.cellsNumeric866 MergedCutGroups.Batch072.populationMatches866
    PopulationCertificates.Batch028.valid577 PopulationCertificates.Batch028.sound577 WitnessCertificates.Batch028.valid577 WitnessCertificates.Batch028.sound577 CountingCertificates.Batch028.valid577 CountingCertificates.Batch028.sound577 H st hI
theorem probabilityBound288 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate866).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate577).dm (WitnessCertificates.Batch028.certificate577).beta (WitnessCertificates.Batch028.certificate577).L) ≤ ((CutFailureCertificates.Budget028.certificate577).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound577 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate577).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate866).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate577).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate577).bound:ℝ) at hb
  exact (exponentialBound288 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches289 : (MergedCutGroups.Batch072.certificate869).AnchorMatches CountingCertificates.Batch028.certificate579 := by decide +kernel
theorem exponentialBound289 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate869).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate579).dm (WitnessCertificates.Batch028.certificate579).beta (WitnessCertificates.Batch028.certificate579).L) ≤ (2*exp (-((CountingCertificates.Batch028.certificate579).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch072.certificate869).exponent:ℝ)*st.R))/((WitnessCertificates.Batch028.certificate579).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch072.certificate869 CountingCertificates.Batch028.certificate579 matches289 MergedCutGroups.Batch072.numericValid869 MergedCutGroups.Batch072.cellsSound869 MergedCutGroups.Batch072.cellsNumeric869 MergedCutGroups.Batch072.populationMatches869
    PopulationCertificates.Batch028.valid579 PopulationCertificates.Batch028.sound579 WitnessCertificates.Batch028.valid579 WitnessCertificates.Batch028.sound579 CountingCertificates.Batch028.valid579 CountingCertificates.Batch028.sound579 H st hI
theorem probabilityBound289 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate869).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch028.certificate579).dm (WitnessCertificates.Batch028.certificate579).beta (WitnessCertificates.Batch028.certificate579).L) ≤ ((CutFailureCertificates.Budget028.certificate579).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget028.sound579 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch028.certificate579).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate869).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch028.certificate579).omega:ℝ)) ≤ ((CutFailureCertificates.Budget028.certificate579).bound:ℝ) at hb
  exact (exponentialBound289 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches290 : (MergedCutGroups.Batch072.certificate872).AnchorMatches CountingCertificates.Batch029.certificate581 := by decide +kernel
theorem exponentialBound290 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate872).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate581).dm (WitnessCertificates.Batch029.certificate581).beta (WitnessCertificates.Batch029.certificate581).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate581).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch072.certificate872).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate581).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch072.certificate872 CountingCertificates.Batch029.certificate581 matches290 MergedCutGroups.Batch072.numericValid872 MergedCutGroups.Batch072.cellsSound872 MergedCutGroups.Batch072.cellsNumeric872 MergedCutGroups.Batch072.populationMatches872
    PopulationCertificates.Batch029.valid581 PopulationCertificates.Batch029.sound581 WitnessCertificates.Batch029.valid581 WitnessCertificates.Batch029.sound581 CountingCertificates.Batch029.valid581 CountingCertificates.Batch029.sound581 H st hI
theorem probabilityBound290 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate872).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate581).dm (WitnessCertificates.Batch029.certificate581).beta (WitnessCertificates.Batch029.certificate581).L) ≤ ((CutFailureCertificates.Budget029.certificate581).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound581 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate581).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate872).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate581).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate581).bound:ℝ) at hb
  exact (exponentialBound290 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches291 : (MergedCutGroups.Batch072.certificate875).AnchorMatches CountingCertificates.Batch029.certificate583 := by decide +kernel
theorem exponentialBound291 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate875).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate583).dm (WitnessCertificates.Batch029.certificate583).beta (WitnessCertificates.Batch029.certificate583).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate583).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch072.certificate875).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate583).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch072.certificate875 CountingCertificates.Batch029.certificate583 matches291 MergedCutGroups.Batch072.numericValid875 MergedCutGroups.Batch072.cellsSound875 MergedCutGroups.Batch072.cellsNumeric875 MergedCutGroups.Batch072.populationMatches875
    PopulationCertificates.Batch029.valid583 PopulationCertificates.Batch029.sound583 WitnessCertificates.Batch029.valid583 WitnessCertificates.Batch029.sound583 CountingCertificates.Batch029.valid583 CountingCertificates.Batch029.sound583 H st hI
theorem probabilityBound291 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch072.certificate875).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate583).dm (WitnessCertificates.Batch029.certificate583).beta (WitnessCertificates.Batch029.certificate583).L) ≤ ((CutFailureCertificates.Budget029.certificate583).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound583 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate583).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch072.certificate875).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate583).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate583).bound:ℝ) at hb
  exact (exponentialBound291 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches292 : (MergedCutGroups.Batch073.certificate878).AnchorMatches CountingCertificates.Batch029.certificate585 := by decide +kernel
theorem exponentialBound292 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate878).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate585).dm (WitnessCertificates.Batch029.certificate585).beta (WitnessCertificates.Batch029.certificate585).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate585).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch073.certificate878).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate585).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch073.certificate878 CountingCertificates.Batch029.certificate585 matches292 MergedCutGroups.Batch073.numericValid878 MergedCutGroups.Batch073.cellsSound878 MergedCutGroups.Batch073.cellsNumeric878 MergedCutGroups.Batch073.populationMatches878
    PopulationCertificates.Batch029.valid585 PopulationCertificates.Batch029.sound585 WitnessCertificates.Batch029.valid585 WitnessCertificates.Batch029.sound585 CountingCertificates.Batch029.valid585 CountingCertificates.Batch029.sound585 H st hI
theorem probabilityBound292 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate878).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate585).dm (WitnessCertificates.Batch029.certificate585).beta (WitnessCertificates.Batch029.certificate585).L) ≤ ((CutFailureCertificates.Budget029.certificate585).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound585 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate585).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate878).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate585).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate585).bound:ℝ) at hb
  exact (exponentialBound292 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches293 : (MergedCutGroups.Batch073.certificate881).AnchorMatches CountingCertificates.Batch029.certificate587 := by decide +kernel
theorem exponentialBound293 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate881).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate587).dm (WitnessCertificates.Batch029.certificate587).beta (WitnessCertificates.Batch029.certificate587).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate587).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch073.certificate881).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate587).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch073.certificate881 CountingCertificates.Batch029.certificate587 matches293 MergedCutGroups.Batch073.numericValid881 MergedCutGroups.Batch073.cellsSound881 MergedCutGroups.Batch073.cellsNumeric881 MergedCutGroups.Batch073.populationMatches881
    PopulationCertificates.Batch029.valid587 PopulationCertificates.Batch029.sound587 WitnessCertificates.Batch029.valid587 WitnessCertificates.Batch029.sound587 CountingCertificates.Batch029.valid587 CountingCertificates.Batch029.sound587 H st hI
theorem probabilityBound293 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate881).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate587).dm (WitnessCertificates.Batch029.certificate587).beta (WitnessCertificates.Batch029.certificate587).L) ≤ ((CutFailureCertificates.Budget029.certificate587).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound587 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate587).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate881).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate587).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate587).bound:ℝ) at hb
  exact (exponentialBound293 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches294 : (MergedCutGroups.Batch073.certificate884).AnchorMatches CountingCertificates.Batch029.certificate589 := by decide +kernel
theorem exponentialBound294 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate884).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate589).dm (WitnessCertificates.Batch029.certificate589).beta (WitnessCertificates.Batch029.certificate589).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate589).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch073.certificate884).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate589).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch073.certificate884 CountingCertificates.Batch029.certificate589 matches294 MergedCutGroups.Batch073.numericValid884 MergedCutGroups.Batch073.cellsSound884 MergedCutGroups.Batch073.cellsNumeric884 MergedCutGroups.Batch073.populationMatches884
    PopulationCertificates.Batch029.valid589 PopulationCertificates.Batch029.sound589 WitnessCertificates.Batch029.valid589 WitnessCertificates.Batch029.sound589 CountingCertificates.Batch029.valid589 CountingCertificates.Batch029.sound589 H st hI
theorem probabilityBound294 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate884).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate589).dm (WitnessCertificates.Batch029.certificate589).beta (WitnessCertificates.Batch029.certificate589).L) ≤ ((CutFailureCertificates.Budget029.certificate589).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound589 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate589).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate884).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate589).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate589).bound:ℝ) at hb
  exact (exponentialBound294 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches295 : (MergedCutGroups.Batch073.certificate887).AnchorMatches CountingCertificates.Batch029.certificate591 := by decide +kernel
theorem exponentialBound295 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate887).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate591).dm (WitnessCertificates.Batch029.certificate591).beta (WitnessCertificates.Batch029.certificate591).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate591).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch073.certificate887).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate591).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch073.certificate887 CountingCertificates.Batch029.certificate591 matches295 MergedCutGroups.Batch073.numericValid887 MergedCutGroups.Batch073.cellsSound887 MergedCutGroups.Batch073.cellsNumeric887 MergedCutGroups.Batch073.populationMatches887
    PopulationCertificates.Batch029.valid591 PopulationCertificates.Batch029.sound591 WitnessCertificates.Batch029.valid591 WitnessCertificates.Batch029.sound591 CountingCertificates.Batch029.valid591 CountingCertificates.Batch029.sound591 H st hI
theorem probabilityBound295 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch073.certificate887).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate591).dm (WitnessCertificates.Batch029.certificate591).beta (WitnessCertificates.Batch029.certificate591).L) ≤ ((CutFailureCertificates.Budget029.certificate591).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound591 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate591).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch073.certificate887).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate591).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate591).bound:ℝ) at hb
  exact (exponentialBound295 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches296 : (MergedCutGroups.Batch074.certificate890).AnchorMatches CountingCertificates.Batch029.certificate593 := by decide +kernel
theorem exponentialBound296 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate890).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate593).dm (WitnessCertificates.Batch029.certificate593).beta (WitnessCertificates.Batch029.certificate593).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate593).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch074.certificate890).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate593).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch074.certificate890 CountingCertificates.Batch029.certificate593 matches296 MergedCutGroups.Batch074.numericValid890 MergedCutGroups.Batch074.cellsSound890 MergedCutGroups.Batch074.cellsNumeric890 MergedCutGroups.Batch074.populationMatches890
    PopulationCertificates.Batch029.valid593 PopulationCertificates.Batch029.sound593 WitnessCertificates.Batch029.valid593 WitnessCertificates.Batch029.sound593 CountingCertificates.Batch029.valid593 CountingCertificates.Batch029.sound593 H st hI
theorem probabilityBound296 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate890).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate593).dm (WitnessCertificates.Batch029.certificate593).beta (WitnessCertificates.Batch029.certificate593).L) ≤ ((CutFailureCertificates.Budget029.certificate593).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound593 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate593).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate890).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate593).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate593).bound:ℝ) at hb
  exact (exponentialBound296 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches297 : (MergedCutGroups.Batch074.certificate893).AnchorMatches CountingCertificates.Batch029.certificate595 := by decide +kernel
theorem exponentialBound297 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate893).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate595).dm (WitnessCertificates.Batch029.certificate595).beta (WitnessCertificates.Batch029.certificate595).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate595).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch074.certificate893).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate595).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch074.certificate893 CountingCertificates.Batch029.certificate595 matches297 MergedCutGroups.Batch074.numericValid893 MergedCutGroups.Batch074.cellsSound893 MergedCutGroups.Batch074.cellsNumeric893 MergedCutGroups.Batch074.populationMatches893
    PopulationCertificates.Batch029.valid595 PopulationCertificates.Batch029.sound595 WitnessCertificates.Batch029.valid595 WitnessCertificates.Batch029.sound595 CountingCertificates.Batch029.valid595 CountingCertificates.Batch029.sound595 H st hI
theorem probabilityBound297 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate893).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate595).dm (WitnessCertificates.Batch029.certificate595).beta (WitnessCertificates.Batch029.certificate595).L) ≤ ((CutFailureCertificates.Budget029.certificate595).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound595 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate595).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate893).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate595).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate595).bound:ℝ) at hb
  exact (exponentialBound297 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches298 : (MergedCutGroups.Batch074.certificate896).AnchorMatches CountingCertificates.Batch029.certificate597 := by decide +kernel
theorem exponentialBound298 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate896).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate597).dm (WitnessCertificates.Batch029.certificate597).beta (WitnessCertificates.Batch029.certificate597).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate597).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch074.certificate896).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate597).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch074.certificate896 CountingCertificates.Batch029.certificate597 matches298 MergedCutGroups.Batch074.numericValid896 MergedCutGroups.Batch074.cellsSound896 MergedCutGroups.Batch074.cellsNumeric896 MergedCutGroups.Batch074.populationMatches896
    PopulationCertificates.Batch029.valid597 PopulationCertificates.Batch029.sound597 WitnessCertificates.Batch029.valid597 WitnessCertificates.Batch029.sound597 CountingCertificates.Batch029.valid597 CountingCertificates.Batch029.sound597 H st hI
theorem probabilityBound298 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate896).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate597).dm (WitnessCertificates.Batch029.certificate597).beta (WitnessCertificates.Batch029.certificate597).L) ≤ ((CutFailureCertificates.Budget029.certificate597).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound597 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate597).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate896).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate597).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate597).bound:ℝ) at hb
  exact (exponentialBound298 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches299 : (MergedCutGroups.Batch074.certificate899).AnchorMatches CountingCertificates.Batch029.certificate599 := by decide +kernel
theorem exponentialBound299 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate899).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate599).dm (WitnessCertificates.Batch029.certificate599).beta (WitnessCertificates.Batch029.certificate599).L) ≤ (2*exp (-((CountingCertificates.Batch029.certificate599).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch074.certificate899).exponent:ℝ)*st.R))/((WitnessCertificates.Batch029.certificate599).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch074.certificate899 CountingCertificates.Batch029.certificate599 matches299 MergedCutGroups.Batch074.numericValid899 MergedCutGroups.Batch074.cellsSound899 MergedCutGroups.Batch074.cellsNumeric899 MergedCutGroups.Batch074.populationMatches899
    PopulationCertificates.Batch029.valid599 PopulationCertificates.Batch029.sound599 WitnessCertificates.Batch029.valid599 WitnessCertificates.Batch029.sound599 CountingCertificates.Batch029.valid599 CountingCertificates.Batch029.sound599 H st hI
theorem probabilityBound299 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch074.certificate899).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch029.certificate599).dm (WitnessCertificates.Batch029.certificate599).beta (WitnessCertificates.Batch029.certificate599).L) ≤ ((CutFailureCertificates.Budget029.certificate599).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget029.sound599 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch029.certificate599).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch074.certificate899).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch029.certificate599).omega:ℝ)) ≤ ((CutFailureCertificates.Budget029.certificate599).bound:ℝ) at hb
  exact (exponentialBound299 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch014
