import Cycle12.ActualCoreRemainder12
import Cycle12.ActualMatchingClosure12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem unusedRequest_survives (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) (hj : ¬F.actualUsedRequest P Q D hi r j) :
    (F.actualRoutes P Q D hi r j).edgeSet⊆(F.coreUnusedGraph P Q D hi r).edgeSet := by
  intro e he
  rw [coreUnusedGraph,edgeSet_deleteEdges]
  refine ⟨F.actualRoutes_edges_core P Q D hi r j he,?_⟩
  rintro ⟨k,hk,he'⟩
  have hne : j≠k := fun h => hj (h ▸ hk)
  exact Set.disjoint_left.mp (F.actualRoutes_disjoint P Q D hi r hne) he he'

theorem core_route_partition (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    (F.coreUnusedGraph P Q D hi r).edgeSet∪F.coreUsedRoutes P Q D hi r=
      (L.foldCorePiece i r).graph.edgeSet ∧
    Disjoint (F.coreUnusedGraph P Q D hi r).edgeSet (F.coreUsedRoutes P Q D hi r) := by
  rw [coreUnusedGraph,edgeSet_deleteEdges]
  exact ⟨Set.sdiff_union_of_subset (F.coreUsedRoutes_core P Q D hi r),Set.disjoint_sdiff_left⟩

theorem coreUsedRoutes_disjoint (hi : i≤L.stopIndex) : Pairwise (fun r t : L.FoldCoreIndex i =>
    Disjoint (F.coreUsedRoutes P Q D hi r) (F.coreUsedRoutes P Q D hi t)) := by
  intro r t hrt
  exact (L.fold_core_edge_disjoint hi hrt).mono (F.coreUsedRoutes_core P Q D hi r)
    (F.coreUsedRoutes_core P Q D hi t)

theorem coreUnused_used_disjoint (hi : i≤L.stopIndex) (r t : L.FoldCoreIndex i) :
    Disjoint (F.coreUnusedGraph P Q D hi r).edgeSet (F.coreUsedRoutes P Q D hi t) := by
  by_cases h : r=t
  · subst t
    exact (F.core_route_partition P Q D hi r).2
  · apply (L.fold_core_edge_disjoint hi h).mono
    · rw [coreUnusedGraph,edgeSet_deleteEdges]
      exact Set.sdiff_subset
    · exact F.coreUsedRoutes_core P Q D hi t

theorem coreUsedRoutes_descendants (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (z : L.FoldBoxIndex i) :
    Disjoint (F.coreUsedRoutes P Q D hi r) (L.foldDescendantGraph i z).edgeSet :=
  (L.fold_core_descendants_disjoint hi r.1 z r.2).mono
    (F.coreUsedRoutes_core P Q D hi r) subset_rfl

theorem coreCompletion_used_disjoint (hi : i≤L.stopIndex) (r t : L.FoldCoreIndex i) :
    Disjoint (F.coreCompletionGraph P Q D hi r).edgeSet (F.coreUsedRoutes P Q D hi t) := by
  rw [coreCompletionGraph,edgeSet_sup,edgeSet_sup,Set.disjoint_union_left,Set.disjoint_union_left]
  refine ⟨⟨F.coreUnused_used_disjoint P Q D hi r t,?_⟩,?_⟩
  · exact (F.coreUsedRoutes_descendants P Q D hi t r.1).symm.mono
      (edgeSet_mono (F.coreRaw_le_descendant P r)) subset_rfl
  · exact (F.coreUsedRoutes_descendants P Q D hi t r.1).symm.mono
      (edgeSet_mono (F.coreHighPairs P r).graph_le) subset_rfl

theorem boxRoute_is_used (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.ActualJointFamily P Q D hi z).Index)
    (hj : F.actualUsedRequest P Q D hi ⟨z,(F.ActualJointFamily P Q D hi z).owner j⟩ ⟨j,rfl⟩) :
    (F.boxRoute P Q D hi z j).edgeSet⊆
      F.coreUsedRoutes P Q D hi ⟨z,(F.ActualJointFamily P Q D hi z).owner j⟩ :=
  fun _ he => ⟨⟨j,rfl⟩,hj,he⟩

theorem matchingRoute_is_used (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (label : Sym2 (Option ((F.active t.1).Index t.2))) (j : F.ClassMatchingIndex P t label) :
    (F.classMatchingRoute P Q D hi t label j).edgeSet⊆
      ⋃ r : L.FoldCoreIndex i,F.coreUsedRoutes P Q D hi r := by
  intro e he
  apply Set.mem_iUnion.mpr
  refine ⟨⟨t.1,(F.ActualJointFamily P Q D hi t.1).owner (.inr (.inl ⟨t.2,⟨label,j⟩⟩))⟩,?_⟩
  exact F.boxRoute_is_used P Q D hi t.1 (.inr (.inl ⟨t.2,⟨label,j⟩⟩)) trivial he

theorem quotientRoute_is_used (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (j : Fin (Q t).count) (z : ((D t).outline j).Switch) :
    (F.actualQuotientRoute P Q D hi t j z).edgeSet⊆
      ⋃ r : L.FoldCoreIndex i,F.coreUsedRoutes P Q D hi r := by
  intro e he
  apply Set.mem_iUnion.mpr
  refine ⟨⟨t.1,(F.ActualJointFamily P Q D hi t.1).owner (.inr (.inr ⟨t.2,⟨j,z⟩⟩))⟩,?_⟩
  exact F.boxRoute_is_used P Q D hi t.1 (.inr (.inr ⟨t.2,⟨j,z⟩⟩)) trivial he

end ActualFoldStage12
end
end Cycle12.Even12
