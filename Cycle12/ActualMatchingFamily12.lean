import Cycle12.OwnedEndpointFamily12
import Cycle12.ActualFoldPairs12
import Cycle12.ActualQuotientPorts12

namespace Cycle12.PreparedBlockBatch12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ}

theorem matchingEdges_subset (P : PreparedBlockBatch12 G A Q) : P.matchingEdges⊆G.edgeSet := by
  intro f hf
  obtain ⟨e,he⟩ := Set.mem_iUnion.mp hf
  exact edgeSet_mono (show edgeLabelGraph G (blockLabel A) e ≤ G from fun _ _ h => h.1)
    ((P.classes e).ledger.matching_subset he)

end
end Cycle12.PreparedBlockBatch12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

def ambientMatchingEdges (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) : Set (Sym2 V) :=
  Sym2.map (Function.Embedding.subtype _ : F.batchVertices t ↪ V) '' (P t).matchingEdges

def ambientMatchingFamily (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) : OwnedEndpointFamily12 (L.foldDescendantGraph i t.1)
      (fun r : Fin (L.foldCores i t.1).length => ((L.foldCores i t.1).get r).vertices)
      (F.ambientMatchingEdges P t) :=
  ((P t).matchingFamily (F.batchActive_disjoint t)).map (Function.Embedding.subtype _)
    ((F.active t.1).router t.2) (fun {_ _} h => (F.batches t.1).graph_le t.2 h)
    (fun r v hv => (F.active t.1).subset_router t.2 r ((mem_verticesWithin _ _ v).mp hv))

theorem ambientMatching_subset (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) : F.ambientMatchingEdges P t⊆(F.batchGraph t).edgeSet := by
  rintro _ ⟨e,he,rfl⟩
  have hh := (P t).matchingEdges_subset he
  induction e using Sym2.inductionOn with
  | _ x y => exact hh

theorem ambientMatching_good (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) (j : (F.ambientMatchingFamily P t).Index) :
    (F.ambientMatchingFamily P t).left j∈F.activeVertices t.1 ∧
      (F.ambientMatchingFamily P t).right j∈F.activeVertices t.1 := by
  let R := (P t).matchingFamily (F.batchActive_disjoint t)
  have hgood (v : F.batchVertices t) (hv : v∈F.batchActive t (R.owner j)) :
      v.val∈F.activeVertices t.1 :=
    mem_biUnion.mpr ⟨t.2,mem_univ _,mem_biUnion.mpr
      ⟨R.owner j,mem_univ _,(mem_verticesWithin _ _ v).mp hv⟩⟩
  exact ⟨hgood _ (R.left_mem j),hgood _ (R.right_mem j)⟩

def boxMatchingEdges (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (z : L.FoldBoxIndex i) : Set (Sym2 V) := ⋃ t,F.ambientMatchingEdges P ⟨z,t⟩

theorem ambientMatching_disjoint (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (z : L.FoldBoxIndex i) : Pairwise (fun t u =>
      Disjoint (F.ambientMatchingEdges P ⟨z,t⟩) (F.ambientMatchingEdges P ⟨z,u⟩)) := by
  intro t u htu
  exact ((F.batches z).disjoint htu).mono (F.ambientMatching_subset P ⟨z,t⟩)
    (F.ambientMatching_subset P ⟨z,u⟩)

def boxMatchingFamily (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (z : L.FoldBoxIndex i) : OwnedEndpointFamily12 (L.foldDescendantGraph i z)
      (fun r : Fin (L.foldCores i z).length => ((L.foldCores i z).get r).vertices)
      (F.boxMatchingEdges P z) :=
  OwnedEndpointFamily12.sigma (fun t => F.ambientMatchingFamily P ⟨z,t⟩)
    (F.ambientMatching_disjoint P z)

theorem boxMatching_good (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (z : L.FoldBoxIndex i) (j : (F.boxMatchingFamily P z).Index) :
    (F.boxMatchingFamily P z).left j∈F.activeVertices z ∧
      (F.boxMatchingFamily P z).right j∈F.activeVertices z :=
  F.ambientMatching_good P ⟨z,j.1⟩ j.2

theorem ambient_pairs_matching (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) : Disjoint (F.ambientBatchPairs P t).used (F.ambientMatchingEdges P t) := by
  rw [ambientBatchPairs,OwnedTwoEdgeFamily12.map_used]
  exact Set.disjoint_image_of_injective (Sym2.map.injective Subtype.val_injective)
    (P t).pairs_matching
  all_goals exact fun {_ _} h => (F.batches t.1).graph_le t.2 h

theorem ambient_pairs_retained (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) : Disjoint (F.ambientBatchPairs P t).used (F.ambientBatchRetained P t).edgeSet := by
  rw [ambientBatchPairs,OwnedTwoEdgeFamily12.map_used,ambientBatchRetained,SimpleGraph.edgeSet_map]
  exact Set.disjoint_image_of_injective (Sym2.map.injective Subtype.val_injective)
    (P t).pairs_retained
  all_goals exact fun {_ _} h => (F.batches t.1).graph_le t.2 h

theorem ambient_matching_retained (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) : Disjoint (F.ambientMatchingEdges P t) (F.ambientBatchRetained P t).edgeSet := by
  rw [ambientMatchingEdges,ambientBatchRetained,SimpleGraph.edgeSet_map]
  exact Set.disjoint_image_of_injective (Sym2.map.injective Subtype.val_injective)
    (P t).matching_retained

/-- Actual cross-batch path and matching requests charge disjoint original
edge classes even when the batches share vertices. -/
theorem box_pairs_matching (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (z : L.FoldBoxIndex i) : Disjoint (F.boxPairs P z).used (F.boxMatchingEdges P z) := by
  rw [boxPairs,OwnedTwoEdgeFamily12.sigma_used,boxMatchingEdges]
  exact disjoint_classwise_unions (fun t => (F.batchGraph ⟨z,t⟩).edgeSet) _ _
    (F.batches z).disjoint (fun t => F.ambientBatchPairs_used_subset P ⟨z,t⟩)
    (fun t => F.ambientMatching_subset P ⟨z,t⟩) (fun t => F.ambient_pairs_matching P ⟨z,t⟩)

end ActualFoldStage12
end
end Cycle12.Even12
