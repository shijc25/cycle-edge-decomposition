import Cycle12.ActualClosureGraphs12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The subgraph to be replaced at an active fold. Its definition is
independent of preparation choices and routes. -/
def EvenScaleLayers12.foldTargetGraph {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) : SimpleGraph V :=
  fromEdgeSet ((⋃ r : L.FoldCoreIndex i,(L.foldCorePiece i r).graph.edgeSet)∪
    (⋃ z : L.FoldBoxIndex i,(L.foldDescendantGraph i z).edgeSet))

theorem EvenScaleLayers12.foldTarget_edges {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) :
    (L.foldTargetGraph i).edgeSet=(⋃ r : L.FoldCoreIndex i,(L.foldCorePiece i r).graph.edgeSet)∪
      (⋃ z : L.FoldBoxIndex i,(L.foldDescendantGraph i z).edgeSet) := by
  apply edgeSet_from_original_subset (G:=G)
  apply Set.union_subset
  · exact Set.iUnion_subset (fun r => edgeSet_mono (L.fold_core_le_original i r))
  · exact Set.iUnion_subset (fun z => edgeSet_mono ((L.fold_descendant_le_box i z).trans
      ((L.fold_box_le_parent i z).trans (L.fold_parent_le_original i z))))

theorem EvenScaleLayers12.foldTarget_le_original {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) :
    L.foldTargetGraph i≤G := by
  apply edgeSet_subset_edgeSet.mp
  rw [L.foldTarget_edges i]
  exact Set.union_subset (Set.iUnion_subset (fun r => edgeSet_mono (L.fold_core_le_original i r)))
    (Set.iUnion_subset (fun z => edgeSet_mono ((L.fold_descendant_le_box i z).trans
      ((L.fold_box_le_parent i z).trans (L.fold_parent_le_original i z)))))

end
end Cycle12.Even12
