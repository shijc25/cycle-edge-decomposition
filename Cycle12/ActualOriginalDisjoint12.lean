import Cycle12.ActualCorePartition12
import Cycle12.ActualMatchingPayment12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)

def matchingOriginalEdges (t : F.MatchingClassIndex) : Set (Sym2 V) :=
  Sym2.map (Subtype.val : F.batchVertices t.1→V) '' ((P t.1).classes t.2).ledger.matchingEdges

theorem matchingOriginal_subset_ambient (t : F.MatchingClassIndex) :
    F.matchingOriginalEdges P t⊆F.ambientMatchingEdges P t.1 := by
  apply Set.image_mono
  exact fun e he => Set.mem_iUnion.mpr ⟨t.2,he⟩

theorem matchingOriginal_subset_batch (t : F.MatchingClassIndex) :
    F.matchingOriginalEdges P t⊆(F.batchGraph t.1).edgeSet :=
  (F.matchingOriginal_subset_ambient P t).trans (F.ambientMatching_subset P t.1)

theorem matchingOriginal_subset_box (t : F.MatchingClassIndex) :
    F.matchingOriginalEdges P t⊆F.boxMatchingEdges P t.1.1 :=
  fun _ he => Set.mem_iUnion.mpr ⟨t.1.2,F.matchingOriginal_subset_ambient P t he⟩

theorem matchingOriginal_subset_descendant (t : F.MatchingClassIndex) :
    F.matchingOriginalEdges P t⊆(L.foldDescendantGraph i t.1.1).edgeSet :=
  (F.matchingOriginal_subset_box P t).trans (F.boxMatching_subset P t.1.1)

theorem matchingOriginal_cover (z : L.FoldBoxIndex i) :
    (⋃ t : (F.batches z).Index,⋃ e : Sym2 (Option ((F.active z).Index t)),
      F.matchingOriginalEdges P ⟨⟨z,t⟩,e⟩)=F.boxMatchingEdges P z := by
  simp only [matchingOriginalEdges,boxMatchingEdges,ambientMatchingEdges,
    PreparedBlockBatch12.matchingEdges,Set.image_iUnion]
  rfl

theorem matchingOriginal_disjoint : Pairwise (fun t u : F.MatchingClassIndex =>
    Disjoint (F.matchingOriginalEdges P t) (F.matchingOriginalEdges P u)) := by
  intro t u htu
  by_cases h : t.1=u.1
  · rcases t with ⟨t,e⟩
    rcases u with ⟨u,f⟩
    dsimp only at h
    subst u
    have hef : e≠f := by intro he; subst f; exact htu rfl
    apply Set.disjoint_image_of_injective (Sym2.map.injective Subtype.val_injective)
    exact ((edgeLabelGraph_partition (F.localBatchGraph t) (blockLabel (F.batchActive t))).1 hef).mono
      ((P t).classes e).ledger.matching_subset ((P t).classes f).ledger.matching_subset
  · exact (F.batch_graph_disjoint h).mono (F.matchingOriginal_subset_batch P t)
      (F.matchingOriginal_subset_batch P u)

theorem retained_original_disjoint : Pairwise (fun t u : F.BatchIndex =>
    Disjoint (F.ambientBatchRetained P t).edgeSet (F.ambientBatchRetained P u).edgeSet) := by
  intro t u htu
  exact (F.batch_graph_disjoint htu).mono (edgeSet_mono (F.ambient_retained_le P t))
    (edgeSet_mono (F.ambient_retained_le P u))

theorem matching_retained_original_disjoint (t : F.MatchingClassIndex) (u : F.BatchIndex) :
    Disjoint (F.matchingOriginalEdges P t) (F.ambientBatchRetained P u).edgeSet := by
  by_cases h : t.1=u
  · subst u
    exact (F.ambient_matching_retained P t.1).mono_left (F.matchingOriginal_subset_ambient P t)
  · exact (F.batch_graph_disjoint h).mono (F.matchingOriginal_subset_batch P t)
      (edgeSet_mono (F.ambient_retained_le P u))

theorem box_internal_pairs_matching (z : L.FoldBoxIndex i) :
    Disjoint (F.boxInternalEdges P z∪(F.boxPairs P z).used) (F.boxMatchingEdges P z) :=
  Set.disjoint_union_left.mpr ⟨(F.box_internal_disjoint P z).mono_right
    (fun _ he => Or.inl (Or.inr he)),F.box_pairs_matching P z⟩

theorem box_internal_pairs_retained (z : L.FoldBoxIndex i) :
    Disjoint (F.boxInternalEdges P z∪(F.boxPairs P z).used) (F.boxRetainedEdges P z) :=
  Set.disjoint_union_left.mpr ⟨(F.box_internal_disjoint P z).mono_right
    (fun _ he => Or.inr he),F.box_pairs_retained P z⟩

theorem coreAssigned_matching_disjoint (r : L.FoldCoreIndex i) (t : F.MatchingClassIndex) :
    Disjoint (F.coreAssignedOriginalEdges P r) (F.matchingOriginalEdges P t) := by
  by_cases h : r.1=t.1.1
  · apply (F.box_internal_pairs_matching P r.1).mono (F.coreAssigned_subset_original_classes P r)
    rw [h]
    exact F.matchingOriginal_subset_box P t
  · exact (L.fold_descendants_disjoint i h).mono (F.coreAssigned_subset_descendant P r)
      (F.matchingOriginal_subset_descendant P t)

theorem coreAssigned_retained_disjoint (r : L.FoldCoreIndex i) (t : F.BatchIndex) :
    Disjoint (F.coreAssignedOriginalEdges P r) (F.ambientBatchRetained P t).edgeSet := by
  by_cases h : r.1=t.1
  · apply (F.box_internal_pairs_retained P r.1).mono (F.coreAssigned_subset_original_classes P r)
    rw [h]
    exact fun _ he => Set.mem_iUnion.mpr ⟨t.2,he⟩
  · exact (L.fold_descendants_disjoint i h).mono (F.coreAssigned_subset_descendant P r)
      (edgeSet_mono ((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2)))

theorem low_original_disjoint : Pairwise (fun r t : L.FoldCoreIndex i =>
    Disjoint (F.CoreLowPairs P r).used (F.CoreLowPairs P t).used) := by
  intro r t hrt
  exact (F.corePairs_disjoint P hrt).mono (F.coreLow_subset_pairs P r) (F.coreLow_subset_pairs P t)

theorem low_matching_original_disjoint (r : L.FoldCoreIndex i) (t : F.MatchingClassIndex) :
    Disjoint (F.CoreLowPairs P r).used (F.matchingOriginalEdges P t) := by
  by_cases h : r.1=t.1.1
  · apply (F.box_pairs_matching P r.1).mono
    · exact (F.coreLow_subset_pairs P r).trans ((F.boxPairs P r.1).restrict_used_subset _)
    · rw [h]
      exact F.matchingOriginal_subset_box P t
  · exact (L.fold_descendants_disjoint i h).mono (F.CoreLowPairs P r).used_subset
      (F.matchingOriginal_subset_descendant P t)

theorem low_retained_original_disjoint (r : L.FoldCoreIndex i) (t : F.BatchIndex) :
    Disjoint (F.CoreLowPairs P r).used (F.ambientBatchRetained P t).edgeSet := by
  by_cases h : r.1=t.1
  · apply (F.box_pairs_retained P r.1).mono
    · exact (F.coreLow_subset_pairs P r).trans ((F.boxPairs P r.1).restrict_used_subset _)
    · rw [h]
      exact fun _ he => Set.mem_iUnion.mpr ⟨t.2,he⟩
  · exact (L.fold_descendants_disjoint i h).mono (F.CoreLowPairs P r).used_subset
      (edgeSet_mono ((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2)))

variable (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem coreCompletion_matching_original_disjoint (hi : i≤L.stopIndex)
    (r : L.FoldCoreIndex i) (t : F.MatchingClassIndex) :
    Disjoint (F.coreCompletionGraph P Q D hi r).edgeSet (F.matchingOriginalEdges P t) := by
  rw [F.coreCompletion_edges P Q D hi r,Set.disjoint_union_left]
  exact ⟨(F.coreUnused_descendants P Q D hi r t.1.1).mono_right (F.matchingOriginal_subset_descendant P t),
    F.coreAssigned_matching_disjoint P r t⟩

theorem coreCompletion_retained_original_disjoint (hi : i≤L.stopIndex)
    (r : L.FoldCoreIndex i) (t : F.BatchIndex) :
    Disjoint (F.coreCompletionGraph P Q D hi r).edgeSet (F.ambientBatchRetained P t).edgeSet := by
  rw [F.coreCompletion_edges P Q D hi r,Set.disjoint_union_left]
  exact ⟨(F.coreUnused_descendants P Q D hi r t.1).mono_right
    (edgeSet_mono ((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2))),
    F.coreAssigned_retained_disjoint P r t⟩

end ActualFoldStage12
end
end Cycle12.Even12
