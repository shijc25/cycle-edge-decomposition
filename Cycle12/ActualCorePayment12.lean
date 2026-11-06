import Cycle12.ActualHighCenterCompletion12
import Cycle12.ActualPairMatchingBudget12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem total_lowPairCount_le :
    (∑ r : L.FoldCoreIndex i,(Fintype.card (F.CoreLowPairs P r).Index:ℝ))≤F.preparedPairCount P := by
  unfold preparedPairCount
  conv_lhs => rw [Fintype.sum_sigma]
  conv_rhs => rw [Fintype.sum_sigma]
  apply sum_le_sum
  intro z hz
  have hh := F.lowPairCount_le_all P z
  change (∑ r : Fin (L.foldCores i z).length,Fintype.card (F.CoreLowPairs P ⟨z,r⟩).Index)≤
    Fintype.card (Σ t,(P ⟨z,t⟩).pairs.Index) at hh
  rw [Fintype.card_sigma] at hh
  exact_mod_cast hh

/-- The low-palette overhead cancels the exact credit in the actual
high-center completion bound, before any global edge assembly. -/
theorem actual_core_and_low_payment (hi : i≤L.stopIndex) {K : ℝ} (hK : 0≤K)
    (ih : ∀ m,m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ T : CyclePacking H,T.weight≤K*m) :
    ∃ (core : ∀ r : L.FoldCoreIndex i,CyclePacking (F.coreCompletionGraph P Q D hi r))
      (low : ∀ r : L.FoldCoreIndex i,CyclePacking G),
      (∀ r,(low r).used=(F.CoreLowPairs P r).used∪
        (⋃ j,(F.actualLowRoute P Q D hi r j).edgeSet)) ∧
      (∑ r : L.FoldCoreIndex i,((core r).weight+((low r).count:ℝ)))≤
        (1+23/42+K*eta+1/2048)*L.coreMass i+
          F.preparedPairCount P/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ) := by
  choose core hc using fun r => F.actual_core_completion P Q D hi r hK ih
  choose low hl hcount using fun r => F.actual_low_closure P Q D hi r
  refine ⟨core,low,hl,?_⟩
  have hh : ∀ r : L.FoldCoreIndex i,(core r).weight+((low r).count:ℝ)≤
      (1+23/42+K*eta+1/2048)*(L.foldCorePiece i r).vertices.card+
        (Fintype.card (F.CoreLowPairs P r).Index:ℝ)/
          routingTeamSize (logScale (originalLog V) L.stopIndex i) := by
    intro r
    linarith only [hc r,hcount r]
  calc
    _ ≤ ∑ r : L.FoldCoreIndex i,((1+23/42+K*eta+1/2048)*(L.foldCorePiece i r).vertices.card+
        (Fintype.card (F.CoreLowPairs P r).Index:ℝ)/
          routingTeamSize (logScale (originalLog V) L.stopIndex i)) := sum_le_sum (fun r _ => hh r)
    _ = (1+23/42+K*eta+1/2048)*L.coreMass i+
        (∑ r : L.FoldCoreIndex i,(Fintype.card (F.CoreLowPairs P r).Index:ℝ))/
          routingTeamSize (logScale (originalLog V) L.stopIndex i) := by
      rw [sum_add_distrib,←mul_sum,←sum_div,L.fold_core_order_sum i]
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_right (F.total_lowPairCount_le P)
      (Nat.cast_nonneg _)) _

end ActualFoldStage12
end
end Cycle12.Even12
