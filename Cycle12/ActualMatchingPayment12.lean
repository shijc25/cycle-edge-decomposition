import Cycle12.ActualMatchingClosure12
import Cycle12.ActualMatchingClassBudget12
import Cycle12.ActualPairMatchingBudget12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def crossingLabels12 (I : Type) [Fintype I] [DecidableEq I] : Finset (Sym2 (Option I)) :=
  (⊤ : SimpleGraph I).edgeFinset.image (Sym2.map some)

theorem crossingLabels12_mem (r t : I) (hrt : r≠t) : s(some r,some t)∈crossingLabels12 I := by
  exact mem_image.mpr ⟨s(r,t),by simpa only [mem_edgeFinset,mem_edgeSet,top_adj] using hrt,rfl⟩

theorem crossingLabels12_card : (crossingLabels12 I).card=Fintype.card (⊤ : SimpleGraph I).edgeSet := by
  rw [crossingLabels12,card_image_of_injective _ (Sym2.map.injective (Option.some_injective I))]
  simp only [SimpleGraph.edgeFinset,Set.toFinset_card,Fintype.card_eq_nat_card]

theorem PreparedClassLedger12.matching_count_bound {G : SimpleGraph V} {A : I→Finset V}
    {Q : ℕ} {e : Sym2 (Option I)} {H : SimpleGraph V}
    (D : PreparedClassLedger12 G A Q e H) (hQ : 0<Q) :
    (D.matchingGroupCount:ℝ)≤(D.matchingEdges.ncard:ℝ)/(2*Q)+if e∈crossingLabels12 I then 1 else 0 := by
  cases D with
  | crossing r t hrt he P hh =>
    have hc := matchingOriginalGroups_count P.second.residue P.matching P.isMatching hQ
    simpa only [matchingGroupCount,matchingEdges,Fintype.card_fin,he,
      if_pos (crossingLabels12_mem r t hrt)] using hc
  | internal r he hh => simp [matchingGroupCount,matchingEdges]; positivity
  | external he hh => simp [matchingGroupCount,matchingEdges]; positivity
  | outside r he P hh => simp [matchingGroupCount,matchingEdges]; positivity

theorem PreparedBlockBatch12.matching_count_sum {G : SimpleGraph V} {A : I→Finset V}
    {Q : ℕ} (P : PreparedBlockBatch12 G A Q) (hQ : 0<Q) :
    (∑ e : Sym2 (Option I),((P.classes e).ledger.matchingGroupCount:ℝ))≤
      (P.matchingEdges.ncard:ℝ)/(2*Q)+(Fintype.card (⊤ : SimpleGraph I).edgeSet:ℝ) := by
  have hd : Pairwise (fun e f : Sym2 (Option I) =>
      Disjoint (P.classes e).ledger.matchingEdges (P.classes f).ledger.matchingEdges) := by
    intro e f hef
    exact ((edgeLabelGraph_partition G (blockLabel A)).1 hef).mono
      (P.classes e).ledger.matching_subset (P.classes f).ledger.matching_subset
  have he : (∑ e : Sym2 (Option I),((P.classes e).ledger.matchingEdges.ncard:ℝ))=P.matchingEdges.ncard := by
    rw [matchingEdges,ncard_iUnion_disjoint _ hd,Nat.cast_sum]
  have hi : (∑ e : Sym2 (Option I),if e∈crossingLabels12 I then (1:ℝ) else 0)=
      (Fintype.card (⊤ : SimpleGraph I).edgeSet:ℝ) := by
    rw [Finset.sum_boole]
    simp only [filter_mem_eq_inter,univ_inter,crossingLabels12_card]
  have hs := sum_le_sum (fun e (_ : e∈(univ:Finset (Sym2 (Option I)))) =>
    (P.classes e).ledger.matching_count_bound hQ)
  simpa only [sum_add_distrib,←sum_div,he,hi] using hs

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)

abbrev MatchingClassIndex := Σ t : F.BatchIndex,Sym2 (Option ((F.active t.1).Index t.2))

theorem actual_matching_group_payment (hi : i≤L.stopIndex) :
    (∑ t : F.MatchingClassIndex,((P t.1).classes t.2).ledger.matchingGroupCount:ℝ)≤
      F.preparedMatchingMass P/(2*routingTeamSize (logScale (originalLog V) L.stopIndex i))+
        batchFee (logScale (originalLog V) L.stopIndex i)*F.activeMass := by
  have hQ := (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1
  have hs := sum_le_sum (fun t (_ : t∈(univ:Finset F.BatchIndex)) => (P t).matching_count_sum hQ)
  rw [Fintype.sum_sigma]
  apply hs.trans
  rw [sum_add_distrib,←sum_div]
  exact add_le_add_right (F.total_matching_class_budget hi) _

variable (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem actual_matching_family_payment (hi : i≤L.stopIndex) :
    ∃ T : F.MatchingClassIndex→CyclePacking G,
      (∀ t,(T t).used=Sym2.map (Function.Embedding.subtype _ : F.batchVertices t.1 ↪ V) ''
        ((P t.1).classes t.2).ledger.matchingEdges∪
          (⋃ j,(F.classMatchingRoute P Q D hi t.1 t.2 j).edgeSet)) ∧
      (∑ t : F.MatchingClassIndex,((T t).count:ℝ))≤
        F.preparedMatchingMass P/(2*routingTeamSize (logScale (originalLog V) L.stopIndex i))+
          batchFee (logScale (originalLog V) L.stopIndex i)*F.activeMass := by
  choose T ht hc using fun t : F.MatchingClassIndex => F.actual_matching_class_closure P Q D hi t.1 t.2
  refine ⟨T,ht,?_⟩
  apply le_trans _ (F.actual_matching_group_payment P hi)
  apply sum_le_sum
  intro t ht
  exact_mod_cast hc t

end ActualFoldStage12
end
end Cycle12.Even12
