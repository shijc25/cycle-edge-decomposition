import Cycle12.ActualFoldDisjoint12
import Cycle12.FoldTargetGraph12

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

theorem all_assigned_original_cover :
    (⋃ r : L.FoldCoreIndex i,F.coreAssignedOriginalEdges P r)∪
      (⋃ r : L.FoldCoreIndex i,(F.CoreLowPairs P r).used)∪
        (⋃ t : F.MatchingClassIndex,F.matchingOriginalEdges P t)∪
          (⋃ t : F.BatchIndex,(F.ambientBatchRetained P t).edgeSet)=
            ⋃ z : L.FoldBoxIndex i,(L.foldDescendantGraph i z).edgeSet := by
  apply Set.Subset.antisymm
  · rintro e (((he|he)|he)|he)
    · obtain ⟨r,he⟩ := Set.mem_iUnion.mp he
      exact Set.mem_iUnion.mpr ⟨r.1,F.coreAssigned_subset_descendant P r he⟩
    · obtain ⟨r,he⟩ := Set.mem_iUnion.mp he
      exact Set.mem_iUnion.mpr ⟨r.1,(F.CoreLowPairs P r).used_subset he⟩
    · obtain ⟨t,he⟩ := Set.mem_iUnion.mp he
      exact Set.mem_iUnion.mpr ⟨t.1.1,F.matchingOriginal_subset_descendant P t he⟩
    · obtain ⟨t,he⟩ := Set.mem_iUnion.mp he
      exact Set.mem_iUnion.mpr ⟨t.1,edgeSet_mono
        ((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2)) he⟩
  · intro e he
    obtain ⟨z,he⟩ := Set.mem_iUnion.mp he
    rw [←F.box_original_cover P z,←F.box_core_original_cover P z] at he
    rcases he with ((he|he)|he)|he
    · obtain ⟨r,he⟩ := Set.mem_iUnion.mp he
      exact Or.inl (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨⟨z,r⟩,he⟩)))
    · obtain ⟨r,he⟩ := Set.mem_iUnion.mp he
      exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨z,r⟩,he⟩)))
    · rw [←F.matchingOriginal_cover P z] at he
      obtain ⟨t,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨label,he⟩ := Set.mem_iUnion.mp he
      exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨⟨z,t⟩,label⟩,he⟩))
    · obtain ⟨t,he⟩ := Set.mem_iUnion.mp he
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨z,t⟩,he⟩)

variable (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

/-- Every selected core edge and every frontier edge occurs in the four
constructed families. This includes unused auxiliary routing edges and
all quotient singleton representatives. -/
theorem foldPiece_cover (hi : i≤L.stopIndex) :
    (⋃ t : F.FoldPieceIndex,(F.foldPieceGraph P Q D hi t).edgeSet)=
      (⋃ r : L.FoldCoreIndex i,(L.foldCorePiece i r).graph.edgeSet)∪
        (⋃ z : L.FoldBoxIndex i,(L.foldDescendantGraph i z).edgeSet) := by
  have hcore : (⋃ r : L.FoldCoreIndex i,(F.coreUnusedGraph P Q D hi r).edgeSet)∪
      (⋃ r : L.FoldCoreIndex i,F.coreUsedRoutes P Q D hi r)=
        ⋃ r : L.FoldCoreIndex i,(L.foldCorePiece i r).graph.edgeSet := by
    rw [←Set.iUnion_union_distrib]
    simp_rw [(F.core_route_partition P Q D hi _).1]
  have ho := F.all_assigned_original_cover P
  have hr := F.all_used_routes_cover P Q D hi
  simp only [Set.iUnion_sum,foldPieceGraph,Sum.elim_inl,Sum.elim_inr]
  simp_rw [F.coreCompletion_edges P Q D hi,F.actualLowGraph_edges P Q D hi,
    F.actualMatchingGraph_edges P Q D hi,F.actualQuotientGraph_edges P Q D hi]
  simp only [Set.iUnion_union_distrib]
  ext e
  have hc := Set.ext_iff.mp hcore e
  have ha := Set.ext_iff.mp ho e
  have ht := Set.ext_iff.mp hr e
  simp only [Set.mem_union] at hc ha ht ⊢
  tauto

theorem foldPiece_le_target (hi : i≤L.stopIndex) (t : F.FoldPieceIndex) :
    F.foldPieceGraph P Q D hi t≤L.foldTargetGraph i := by
  apply edgeSet_subset_edgeSet.mp
  rw [L.foldTarget_edges i,←F.foldPiece_cover P Q D hi]
  exact fun _ he => Set.mem_iUnion.mpr ⟨t,he⟩

end ActualFoldStage12
end
end Cycle12.Even12
