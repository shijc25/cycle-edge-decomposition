import Cycle12.ActualClosureGraphs12
import Cycle12.ActualRouteDisjoint12

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
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem core_matching_disjoint (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) (t : F.MatchingClassIndex) :
    Disjoint (F.coreCompletionGraph P Q D hi r).edgeSet (F.actualMatchingGraph P Q D hi t).edgeSet := by
  rw [F.actualMatchingGraph_edges P Q D hi t,Set.disjoint_union_right]
  refine ⟨F.coreCompletion_matching_original_disjoint P Q D hi r t,?_⟩
  apply (Set.disjoint_iUnion_right.mpr (fun u => F.coreCompletion_used_disjoint P Q D hi r u)).mono_right
  exact Set.iUnion_subset (fun j => F.matchingRoute_is_used P Q D hi t.1 t.2 j)

theorem core_quotient_disjoint (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) (t : F.BatchIndex) :
    Disjoint (F.coreCompletionGraph P Q D hi r).edgeSet (F.actualQuotientGraph P Q D hi t).edgeSet := by
  rw [F.actualQuotientGraph_edges P Q D hi t,Set.disjoint_union_right]
  refine ⟨F.coreCompletion_retained_original_disjoint P Q D hi r t,?_⟩
  apply (Set.disjoint_iUnion_right.mpr (fun u => F.coreCompletion_used_disjoint P Q D hi r u)).mono_right
  exact Set.iUnion_subset (fun j => Set.iUnion_subset (fun z => F.quotientRoute_is_used P Q D hi t j z))

theorem actualLowGraph_disjoint (hi : i≤L.stopIndex) : Pairwise (fun r t : L.FoldCoreIndex i =>
    Disjoint (F.actualLowGraph P Q D hi r).edgeSet (F.actualLowGraph P Q D hi t).edgeSet) := by
  intro r t hrt
  rw [F.actualLowGraph_edges P Q D hi r,F.actualLowGraph_edges P Q D hi t,
    Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
  exact ⟨⟨F.low_original_disjoint P hrt,
    (F.lowRouteEdges_descendants P Q D hi t r.1).symm.mono_left (F.CoreLowPairs P r).used_subset⟩,
    ⟨(F.lowRouteEdges_descendants P Q D hi r t.1).mono_right (F.CoreLowPairs P t).used_subset,
      F.lowRouteEdges_disjoint P Q D hi hrt⟩⟩

theorem low_matching_disjoint (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) (t : F.MatchingClassIndex) :
    Disjoint (F.actualLowGraph P Q D hi r).edgeSet (F.actualMatchingGraph P Q D hi t).edgeSet := by
  rw [F.actualLowGraph_edges P Q D hi r,F.actualMatchingGraph_edges P Q D hi t,
    Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
  exact ⟨⟨F.low_matching_original_disjoint P r t,
    (F.matchingRouteEdges_descendants P Q D hi t r.1).symm.mono_left (F.CoreLowPairs P r).used_subset⟩,
    ⟨(F.lowRouteEdges_descendants P Q D hi r t.1.1).mono_right (F.matchingOriginal_subset_descendant P t),
      F.low_matching_routes_disjoint P Q D hi r t⟩⟩

theorem low_quotient_disjoint (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) (t : F.BatchIndex) :
    Disjoint (F.actualLowGraph P Q D hi r).edgeSet (F.actualQuotientGraph P Q D hi t).edgeSet := by
  rw [F.actualLowGraph_edges P Q D hi r,F.actualQuotientGraph_edges P Q D hi t,
    Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
  exact ⟨⟨F.low_retained_original_disjoint P r t,
    (F.quotientRouteEdges_descendants P Q D hi t r.1).symm.mono_left (F.CoreLowPairs P r).used_subset⟩,
    ⟨(F.lowRouteEdges_descendants P Q D hi r t.1).mono_right
      (edgeSet_mono ((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2))),
      F.low_quotient_routes_disjoint P Q D hi r t⟩⟩

theorem actualMatchingGraph_disjoint (hi : i≤L.stopIndex) : Pairwise (fun t u : F.MatchingClassIndex =>
    Disjoint (F.actualMatchingGraph P Q D hi t).edgeSet (F.actualMatchingGraph P Q D hi u).edgeSet) := by
  intro t u htu
  rw [F.actualMatchingGraph_edges P Q D hi t,F.actualMatchingGraph_edges P Q D hi u,
    Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
  exact ⟨⟨F.matchingOriginal_disjoint P htu,
    (F.matchingRouteEdges_descendants P Q D hi u t.1.1).symm.mono_left (F.matchingOriginal_subset_descendant P t)⟩,
    ⟨(F.matchingRouteEdges_descendants P Q D hi t u.1.1).mono_right (F.matchingOriginal_subset_descendant P u),
      F.matchingRouteEdges_disjoint P Q D hi htu⟩⟩

theorem matching_quotient_disjoint (hi : i≤L.stopIndex) (t : F.MatchingClassIndex) (u : F.BatchIndex) :
    Disjoint (F.actualMatchingGraph P Q D hi t).edgeSet (F.actualQuotientGraph P Q D hi u).edgeSet := by
  rw [F.actualMatchingGraph_edges P Q D hi t,F.actualQuotientGraph_edges P Q D hi u,
    Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
  exact ⟨⟨F.matching_retained_original_disjoint P t u,
    (F.quotientRouteEdges_descendants P Q D hi u t.1.1).symm.mono_left (F.matchingOriginal_subset_descendant P t)⟩,
    ⟨(F.matchingRouteEdges_descendants P Q D hi t u.1).mono_right
      (edgeSet_mono ((F.ambient_retained_le P u).trans ((F.batches u.1).graph_le u.2))),
      F.matching_quotient_routes_disjoint P Q D hi t u⟩⟩

theorem actualQuotientGraph_disjoint (hi : i≤L.stopIndex) : Pairwise (fun t u : F.BatchIndex =>
    Disjoint (F.actualQuotientGraph P Q D hi t).edgeSet (F.actualQuotientGraph P Q D hi u).edgeSet) := by
  intro t u htu
  rw [F.actualQuotientGraph_edges P Q D hi t,F.actualQuotientGraph_edges P Q D hi u,
    Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
  exact ⟨⟨F.retained_original_disjoint P htu,
    (F.quotientRouteEdges_descendants P Q D hi u t.1).symm.mono_left
      (edgeSet_mono ((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2)))⟩,
    ⟨(F.quotientRouteEdges_descendants P Q D hi t u.1).mono_right
      (edgeSet_mono ((F.ambient_retained_le P u).trans ((F.batches u.1).graph_le u.2))),
      F.quotientRouteEdges_disjoint P Q D hi htu⟩⟩

abbrev FoldPieceIndex := (L.FoldCoreIndex i) ⊕ ((L.FoldCoreIndex i) ⊕ (F.MatchingClassIndex ⊕ F.BatchIndex))

def foldPieceGraph (hi : i≤L.stopIndex) : F.FoldPieceIndex→SimpleGraph V :=
  Sum.elim (F.coreCompletionGraph P Q D hi)
    (Sum.elim (F.actualLowGraph P Q D hi) (Sum.elim (F.actualMatchingGraph P Q D hi) (F.actualQuotientGraph P Q D hi)))

theorem foldPiece_le_original (hi : i≤L.stopIndex) (t : F.FoldPieceIndex) :
    F.foldPieceGraph P Q D hi t≤G := by
  rcases t with t|t|t|t
  · exact F.coreCompletion_le_original P Q D hi t
  · exact F.actualLowGraph_le P Q D hi t
  · exact F.actualMatchingGraph_le P Q D hi t
  · exact F.actualQuotientGraph_le P Q D hi t

theorem foldPiece_disjoint (hi : i≤L.stopIndex) : Pairwise (fun t u : F.FoldPieceIndex =>
    Disjoint (F.foldPieceGraph P Q D hi t).edgeSet (F.foldPieceGraph P Q D hi u).edgeSet) := by
  intro t u htu
  rcases t with t|t|t|t <;> rcases u with u|u|u|u
  · exact F.coreCompletion_disjoint P Q D hi (fun h => htu (congrArg Sum.inl h))
  · rw [show (F.foldPieceGraph P Q D hi (.inr (.inl u))).edgeSet=(F.actualLowGraph P Q D hi u).edgeSet from rfl,
      F.actualLowGraph_edges P Q D hi u]
    exact F.coreCompletion_low_closure_disjoint P Q D hi t u
  · exact F.core_matching_disjoint P Q D hi t u
  · exact F.core_quotient_disjoint P Q D hi t u
  · have hh := F.coreCompletion_low_closure_disjoint P Q D hi u t
    change Disjoint (F.coreCompletionGraph P Q D hi u).edgeSet
      ((F.CoreLowPairs P t).used ∪ F.lowRouteEdges P Q D hi t) at hh
    rw [←F.actualLowGraph_edges P Q D hi t] at hh
    exact hh.symm
  · exact F.actualLowGraph_disjoint P Q D hi (fun h => htu (congrArg (Sum.inr ∘ Sum.inl) h))
  · exact F.low_matching_disjoint P Q D hi t u
  · exact F.low_quotient_disjoint P Q D hi t u
  · exact (F.core_matching_disjoint P Q D hi u t).symm
  · exact (F.low_matching_disjoint P Q D hi u t).symm
  · exact F.actualMatchingGraph_disjoint P Q D hi (fun h => htu (congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) h))
  · exact F.matching_quotient_disjoint P Q D hi t u
  · exact (F.core_quotient_disjoint P Q D hi u t).symm
  · exact (F.low_quotient_disjoint P Q D hi u t).symm
  · exact (F.matching_quotient_disjoint P Q D hi u t).symm
  · exact F.actualQuotientGraph_disjoint P Q D hi (fun h => htu (congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inr) h))

end ActualFoldStage12
end
end Cycle12.Even12
