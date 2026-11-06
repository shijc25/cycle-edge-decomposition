import Cycle12.ActualOriginalDisjoint12
import Cycle12.ActualQuotientAssembly12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem edgeSet_from_original_subset {G : SimpleGraph V} {S : Set (Sym2 V)} (hS : S⊆G.edgeSet) :
    (fromEdgeSet S).edgeSet=S := by
  rw [edgeSet_fromEdgeSet]
  exact Set.Subset.antisymm Set.sdiff_subset
    (fun _ he => ⟨he,G.edgeSet_subset_compl_diagSet (hS he)⟩)

/-- A partial packing has no leftover singleton charge when viewed on
the graph consisting exactly of its used original edges. -/
theorem restrictPacking_full_weight {G : SimpleGraph V} (P : CyclePacking G)
    (H : SimpleGraph V) (h : P.used=H.edgeSet) :
    (restrictPacking P H h.le).weight=(P.count:ℝ) := by
  have hz : (restrictPacking P H h.le).singles=0 := by
    change (H.deleteEdges P.used).edgeSet.ncard=0
    rw [edgeSet_deleteEdges,h,Set.diff_self,Set.ncard_empty]
  change (P.count:ℝ)+(23/42:ℝ)*(restrictPacking P H h.le).singles=(P.count:ℝ)
  rw [hz,Nat.cast_zero,mul_zero,add_zero]

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
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

def actualLowGraph (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) : SimpleGraph V :=
  fromEdgeSet ((F.CoreLowPairs P r).used∪F.lowRouteEdges P Q D hi r)

theorem actualLowGraph_edges (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    (F.actualLowGraph P Q D hi r).edgeSet=(F.CoreLowPairs P r).used∪F.lowRouteEdges P Q D hi r := by
  apply edgeSet_from_original_subset (G:=G)
  apply Set.union_subset
  · exact (F.CoreLowPairs P r).used_subset.trans (edgeSet_mono
      ((L.fold_descendant_le_box i r.1).trans ((L.fold_box_le_parent i r.1).trans (L.fold_parent_le_original i r.1))))
  · exact Set.iUnion_subset (fun j => (F.actualLowRoute P Q D hi r j).edges_subset_edgeSet)

theorem actualLowGraph_le (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    F.actualLowGraph P Q D hi r≤G := by
  apply edgeSet_subset_edgeSet.mp
  rw [F.actualLowGraph_edges P Q D hi r]
  exact Set.union_subset ((F.CoreLowPairs P r).used_subset.trans (edgeSet_mono
    ((L.fold_descendant_le_box i r.1).trans ((L.fold_box_le_parent i r.1).trans (L.fold_parent_le_original i r.1)))))
    (Set.iUnion_subset (fun j => (F.actualLowRoute P Q D hi r j).edges_subset_edgeSet))

def actualMatchingGraph (hi : i≤L.stopIndex) (t : F.MatchingClassIndex) : SimpleGraph V :=
  fromEdgeSet (F.matchingOriginalEdges P t∪F.matchingRouteEdges P Q D hi t)

theorem actualMatchingGraph_edges (hi : i≤L.stopIndex) (t : F.MatchingClassIndex) :
    (F.actualMatchingGraph P Q D hi t).edgeSet=F.matchingOriginalEdges P t∪F.matchingRouteEdges P Q D hi t := by
  apply edgeSet_from_original_subset (G:=G)
  exact Set.union_subset ((F.matchingOriginal_subset_batch P t).trans (edgeSet_mono (F.batch_graph_le_original t.1)))
    (Set.iUnion_subset (fun j => (F.classMatchingRoute P Q D hi t.1 t.2 j).edges_subset_edgeSet))

theorem actualMatchingGraph_le (hi : i≤L.stopIndex) (t : F.MatchingClassIndex) :
    F.actualMatchingGraph P Q D hi t≤G := by
  apply edgeSet_subset_edgeSet.mp
  rw [F.actualMatchingGraph_edges P Q D hi t]
  exact Set.union_subset ((F.matchingOriginal_subset_batch P t).trans (edgeSet_mono (F.batch_graph_le_original t.1)))
    (Set.iUnion_subset (fun j => (F.classMatchingRoute P Q D hi t.1 t.2 j).edges_subset_edgeSet))

end ActualFoldStage12
end
end Cycle12.Even12
