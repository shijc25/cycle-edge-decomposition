import Cycle12.ActualInnerPairs12
import Cycle12.ActualMatchingFamily12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)

theorem ambient_original_cover (t : F.BatchIndex) :
    F.ambientInternalEdges P t∪(F.ambientBatchPairs P t).used∪
      F.ambientMatchingEdges P t∪(F.ambientBatchRetained P t).edgeSet=(F.batchGraph t).edgeSet := by
  rw [ambientInternalEdges,ambientBatchPairs,OwnedTwoEdgeFamily12.map_used,
    ambientMatchingEdges,ambientBatchRetained,edgeSet_map]
  · change Sym2.map (Subtype.val : F.batchVertices t→V) '' (P t).internalEdges∪
      Sym2.map Subtype.val '' (P t).pairs.used∪Sym2.map Subtype.val '' (P t).matchingEdges∪
      Sym2.map Subtype.val '' (P t).retained.edgeSet=(F.batchGraph t).edgeSet
    rw [←Set.image_union,←Set.image_union,←Set.image_union,(P t).original_cover]
    exact induced_edges_of_supported (F.batchGraph t) (F.batchVertices t)
      (fun _ _ h => (F.batches t.1).supported t.2 h)
  · exact fun {_ _} h => (F.batches t.1).graph_le t.2 h

theorem ambient_internal_disjoint (t : F.BatchIndex) :
    Disjoint (F.ambientInternalEdges P t)
      ((F.ambientBatchPairs P t).used∪F.ambientMatchingEdges P t∪(F.ambientBatchRetained P t).edgeSet) := by
  rw [ambientInternalEdges,ambientBatchPairs,OwnedTwoEdgeFamily12.map_used,
    ambientMatchingEdges,ambientBatchRetained,edgeSet_map]
  · change Disjoint (Sym2.map (Subtype.val : F.batchVertices t→V) '' (P t).internalEdges)
      (Sym2.map Subtype.val '' (P t).pairs.used∪Sym2.map Subtype.val '' (P t).matchingEdges∪
        Sym2.map Subtype.val '' (P t).retained.edgeSet)
    rw [←Set.image_union,←Set.image_union]
    exact Set.disjoint_image_of_injective (Sym2.map.injective Subtype.val_injective) (P t).internal_disjoint
  · exact fun {_ _} h => (F.batches t.1).graph_le t.2 h

def boxRetainedEdges (z : L.FoldBoxIndex i) : Set (Sym2 V) :=
  ⋃ t,(F.ambientBatchRetained P ⟨z,t⟩).edgeSet

theorem boxMatching_subset (z : L.FoldBoxIndex i) :
    F.boxMatchingEdges P z⊆(L.foldDescendantGraph i z).edgeSet := by
  apply Set.iUnion_subset
  intro t
  exact (F.ambientMatching_subset P ⟨z,t⟩).trans (edgeSet_mono ((F.batches z).graph_le t))

theorem boxRetained_subset (z : L.FoldBoxIndex i) :
    F.boxRetainedEdges P z⊆(L.foldDescendantGraph i z).edgeSet := by
  apply Set.iUnion_subset
  intro t
  exact edgeSet_mono ((F.ambient_retained_le P ⟨z,t⟩).trans ((F.batches z).graph_le t))

theorem box_original_cover (z : L.FoldBoxIndex i) :
    F.boxInternalEdges P z∪(F.boxPairs P z).used∪F.boxMatchingEdges P z∪F.boxRetainedEdges P z=
      (L.foldDescendantGraph i z).edgeSet := by
  rw [boxInternalEdges,boxPairs,OwnedTwoEdgeFamily12.sigma_used,boxMatchingEdges,boxRetainedEdges,
    ←Set.iUnion_union_distrib,←Set.iUnion_union_distrib,←Set.iUnion_union_distrib]
  simp_rw [F.ambient_original_cover P]
  exact (F.batches z).edge_cover

theorem box_internal_disjoint (z : L.FoldBoxIndex i) :
    Disjoint (F.boxInternalEdges P z)
      ((F.boxPairs P z).used∪F.boxMatchingEdges P z∪F.boxRetainedEdges P z) := by
  rw [boxInternalEdges,boxPairs,OwnedTwoEdgeFamily12.sigma_used,boxMatchingEdges,boxRetainedEdges,
    ←Set.iUnion_union_distrib,←Set.iUnion_union_distrib]
  apply disjoint_classwise_unions (fun t => (F.batchGraph ⟨z,t⟩).edgeSet) _ _
    (F.batches z).disjoint (fun t => F.ambientInternal_subset P ⟨z,t⟩)
  · intro t
    exact Set.union_subset (Set.union_subset (F.ambientBatchPairs_used_subset P ⟨z,t⟩)
      (F.ambientMatching_subset P ⟨z,t⟩)) (edgeSet_mono (F.ambient_retained_le P ⟨z,t⟩))
  · exact fun t => F.ambient_internal_disjoint P ⟨z,t⟩

theorem box_pairs_retained (z : L.FoldBoxIndex i) :
    Disjoint (F.boxPairs P z).used (F.boxRetainedEdges P z) := by
  rw [boxPairs,OwnedTwoEdgeFamily12.sigma_used,boxRetainedEdges]
  exact disjoint_classwise_unions (fun t => (F.batchGraph ⟨z,t⟩).edgeSet) _ _
    (F.batches z).disjoint (fun t => F.ambientBatchPairs_used_subset P ⟨z,t⟩)
    (fun t => edgeSet_mono (F.ambient_retained_le P ⟨z,t⟩)) (fun t => F.ambient_pairs_retained P ⟨z,t⟩)

theorem box_matching_retained (z : L.FoldBoxIndex i) :
    Disjoint (F.boxMatchingEdges P z) (F.boxRetainedEdges P z) := by
  rw [boxMatchingEdges,boxRetainedEdges]
  exact disjoint_classwise_unions (fun t => (F.batchGraph ⟨z,t⟩).edgeSet) _ _
    (F.batches z).disjoint (fun t => F.ambientMatching_subset P ⟨z,t⟩)
    (fun t => edgeSet_mono (F.ambient_retained_le P ⟨z,t⟩)) (fun t => F.ambient_matching_retained P ⟨z,t⟩)

theorem coreInternal_pairs_disjoint (r t : L.FoldCoreIndex i) :
    Disjoint (F.coreInternalEdges P r) (F.corePairs P t).used := by
  by_cases h : r.1=t.1
  · have hh := (F.box_internal_disjoint P r.1).mono_right
      (show (F.boxPairs P r.1).used⊆(F.boxPairs P r.1).used∪F.boxMatchingEdges P r.1∪F.boxRetainedEdges P r.1
        from fun _ he => Or.inl (Or.inl he))
    apply hh.mono Set.inter_subset_left
    rw [h]
    exact (F.boxPairs P t.1).restrict_used_subset _
  · exact (L.fold_descendants_disjoint i h).mono
      (Set.inter_subset_left.trans (F.boxInternal_subset P r.1)) (F.corePairs P t).used_subset

end ActualFoldStage12
end
end Cycle12.Even12
