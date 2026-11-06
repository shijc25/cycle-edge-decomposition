import Cycle12.ActualOriginalPartition12
import Cycle12.ActualRouteSelection12

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

def corePendingPairEdges (r : L.FoldCoreIndex i) : Set (Sym2 V) :=
  (F.coreInnerPairs P r).used∪(F.coreHighPairs P r).used

theorem corePendingPair_subset (r : L.FoldCoreIndex i) :
    F.corePendingPairEdges P r⊆(F.corePairs P r).used :=
  Set.union_subset ((F.corePairs P r).restrict_used_subset _)
    (((F.coreExternalPairs P r).restrict_used_subset _).trans ((F.corePairs P r).restrict_used_subset _))

theorem coreLow_subset_pairs (r : L.FoldCoreIndex i) :
    (F.CoreLowPairs P r).used⊆(F.corePairs P r).used :=
  ((F.coreExternalPairs P r).restrict_used_subset _).trans ((F.corePairs P r).restrict_used_subset _)

theorem core_pending_low_partition (r : L.FoldCoreIndex i) :
    F.corePendingPairEdges P r∪(F.CoreLowPairs P r).used=(F.corePairs P r).used ∧
      Disjoint (F.corePendingPairEdges P r) (F.CoreLowPairs P r).used := by
  constructor
  · rw [corePendingPairEdges,Set.union_assoc,Set.union_comm (F.coreHighPairs P r).used]
    rw [(F.core_low_high_partition P r).1,(F.core_inner_external_partition P r).1]
  · apply Set.disjoint_union_left.mpr
    exact ⟨(F.core_inner_external_partition P r).2.mono_right
      ((F.coreExternalPairs P r).restrict_used_subset _),(F.core_low_high_partition P r).2.symm⟩

theorem corePending_low_disjoint (r t : L.FoldCoreIndex i) :
    Disjoint (F.corePendingPairEdges P r) (F.CoreLowPairs P t).used := by
  by_cases h : r=t
  · subst t
    exact (F.core_pending_low_partition P r).2
  · exact (F.corePairs_disjoint P h).mono (F.corePendingPair_subset P r) (F.coreLow_subset_pairs P t)

def coreAssignedOriginalEdges (r : L.FoldCoreIndex i) : Set (Sym2 V) :=
  F.coreInternalEdges P r∪F.corePendingPairEdges P r

theorem coreAssigned_subset_descendant (r : L.FoldCoreIndex i) :
    F.coreAssignedOriginalEdges P r⊆(L.foldDescendantGraph i r.1).edgeSet :=
  Set.union_subset (Set.inter_subset_left.trans (F.boxInternal_subset P r.1))
    ((F.corePendingPair_subset P r).trans (F.corePairs P r).used_subset)

theorem coreAssigned_subset_original_classes (r : L.FoldCoreIndex i) :
    F.coreAssignedOriginalEdges P r⊆F.boxInternalEdges P r.1∪(F.boxPairs P r.1).used :=
  Set.union_subset_union Set.inter_subset_left
    ((F.corePendingPair_subset P r).trans ((F.boxPairs P r.1).restrict_used_subset _))

theorem coreAssigned_disjoint (hi : i≤L.stopIndex) : Pairwise (fun r t : L.FoldCoreIndex i =>
    Disjoint (F.coreAssignedOriginalEdges P r) (F.coreAssignedOriginalEdges P t)) := by
  intro r t hrt
  rw [coreAssignedOriginalEdges,coreAssignedOriginalEdges,
    Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
  exact ⟨⟨F.coreInternal_disjoint P hi hrt,(F.coreInternal_pairs_disjoint P r t).mono_right
    (F.corePendingPair_subset P t)⟩,
    ⟨(F.coreInternal_pairs_disjoint P t r).symm.mono_left (F.corePendingPair_subset P r),
      (F.corePairs_disjoint P hrt).mono (F.corePendingPair_subset P r) (F.corePendingPair_subset P t)⟩⟩

theorem coreAssigned_low_disjoint (r t : L.FoldCoreIndex i) :
    Disjoint (F.coreAssignedOriginalEdges P r) (F.CoreLowPairs P t).used :=
  Set.disjoint_union_left.mpr ⟨(F.coreInternal_pairs_disjoint P r t).mono_right
    (F.coreLow_subset_pairs P t),F.corePending_low_disjoint P r t⟩

theorem box_core_original_cover (z : L.FoldBoxIndex i) :
    (⋃ r : Fin (L.foldCores i z).length,F.coreAssignedOriginalEdges P ⟨z,r⟩)∪
      (⋃ r : Fin (L.foldCores i z).length,(F.CoreLowPairs P ⟨z,r⟩).used)=
      F.boxInternalEdges P z∪(F.boxPairs P z).used := by
  rw [←Set.iUnion_union_distrib]
  simp only [coreAssignedOriginalEdges,Set.union_assoc]
  simp_rw [(F.core_pending_low_partition P _).1]
  rw [Set.iUnion_union_distrib,F.coreInternal_cover P z,F.corePairs_cover P z]

variable (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem coreCompletion_edges (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    (F.coreCompletionGraph P Q D hi r).edgeSet=
      (F.coreUnusedGraph P Q D hi r).edgeSet∪F.coreAssignedOriginalEdges P r := by
  simp only [coreCompletionGraph,coreRawGraph,edgeSet_sup,F.coreInternalGraph_edges,
    OwnedTwoEdgeFamily12.graph_edges,coreAssignedOriginalEdges,corePendingPairEdges,Set.union_assoc]

theorem coreUnused_descendants (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) (z : L.FoldBoxIndex i) :
    Disjoint (F.coreUnusedGraph P Q D hi r).edgeSet (L.foldDescendantGraph i z).edgeSet := by
  apply (L.fold_core_descendants_disjoint hi r.1 z r.2).mono
  · rw [coreUnusedGraph,edgeSet_deleteEdges]
    exact Set.sdiff_subset
  · exact subset_rfl

theorem coreCompletion_disjoint (hi : i≤L.stopIndex) : Pairwise (fun r t : L.FoldCoreIndex i =>
    Disjoint (F.coreCompletionGraph P Q D hi r).edgeSet (F.coreCompletionGraph P Q D hi t).edgeSet) := by
  intro r t hrt
  rw [F.coreCompletion_edges P Q D hi r,F.coreCompletion_edges P Q D hi t,
    Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
  refine ⟨⟨?_,?_⟩,⟨?_,F.coreAssigned_disjoint P hi hrt⟩⟩
  · apply (L.fold_core_edge_disjoint hi hrt).mono
    all_goals rw [coreUnusedGraph,edgeSet_deleteEdges]; exact Set.sdiff_subset
  · exact (F.coreUnused_descendants P Q D hi r t.1).mono_right (F.coreAssigned_subset_descendant P t)
  · exact (F.coreUnused_descendants P Q D hi t r.1).symm.mono_left (F.coreAssigned_subset_descendant P r)

theorem coreCompletion_low_original_disjoint (hi : i≤L.stopIndex) (r t : L.FoldCoreIndex i) :
    Disjoint (F.coreCompletionGraph P Q D hi r).edgeSet (F.CoreLowPairs P t).used := by
  rw [F.coreCompletion_edges P Q D hi r,Set.disjoint_union_left]
  exact ⟨(F.coreUnused_descendants P Q D hi r t.1).mono_right (F.CoreLowPairs P t).used_subset,
    F.coreAssigned_low_disjoint P r t⟩

theorem coreCompletion_low_closure_disjoint (hi : i≤L.stopIndex) (r t : L.FoldCoreIndex i) :
    Disjoint (F.coreCompletionGraph P Q D hi r).edgeSet
      ((F.CoreLowPairs P t).used∪⋃ j,(F.actualLowRoute P Q D hi t j).edgeSet) := by
  apply Set.disjoint_union_right.mpr
  refine ⟨F.coreCompletion_low_original_disjoint P Q D hi r t,?_⟩
  apply (F.coreCompletion_used_disjoint P Q D hi r t).mono_right
  exact Set.iUnion_subset (fun j => F.lowRoute_used P Q D hi t j)

end ActualFoldStage12
end
end Cycle12.Even12
