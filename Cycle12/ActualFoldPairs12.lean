import Cycle12.PreparedBatchPaths12
import Cycle12.ActualFoldQuotients12
import Cycle12.ActualCoreRouting12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

/-- Move every prepared two-edge path to its actual original descendant
graph and replace its active-block owner by the selected core owner. -/
def ambientBatchPairs (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (t : F.BatchIndex) :
    OwnedTwoEdgeFamily12 (L.foldDescendantGraph i t.1)
      (fun r : Fin (L.foldCores i t.1).length => ((L.foldCores i t.1).get r).vertices) :=
  (P t).pairs.map (Function.Embedding.subtype _) ((F.active t.1).router t.2)
    (fun {_ _} h => (F.batches t.1).graph_le t.2 h)
    (fun r v hv => (F.active t.1).subset_router t.2 r
      ((mem_verticesWithin _ _ v).mp hv))

theorem ambientBatchPairs_used_subset (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) : (F.ambientBatchPairs P t).used⊆(F.batchGraph t).edgeSet := by
  intro e he
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  rcases hj with rfl|rfl
  · exact (P t).pairs.adj_left j
  · exact (P t).pairs.adj_right j

theorem ambientBatchPairs_good (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (t : F.BatchIndex) (j : (F.ambientBatchPairs P t).Index) :
    (F.ambientBatchPairs P t).left j∈F.activeVertices t.1 ∧
      (F.ambientBatchPairs P t).right j∈F.activeVertices t.1 := by
  have ha := (P t).pairs.left_mem j
  have hb := (P t).pairs.right_mem j
  have hgood (v : F.batchVertices t) (hv : v∈F.batchActive t ((P t).pairs.owner j)) :
      v.val∈F.activeVertices t.1 := by
    exact mem_biUnion.mpr ⟨t.2,mem_univ _,mem_biUnion.mpr
      ⟨(P t).pairs.owner j,mem_univ _,(mem_verticesWithin _ _ v).mp hv⟩⟩
  exact ⟨hgood _ ha,hgood _ hb⟩

theorem ambientBatchPairs_disjoint (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (z : L.FoldBoxIndex i) : Pairwise (fun t u =>
      Disjoint (F.ambientBatchPairs P ⟨z,t⟩).used (F.ambientBatchPairs P ⟨z,u⟩).used) := by
  intro t u htu
  exact ((F.batches z).disjoint htu).mono (F.ambientBatchPairs_used_subset P ⟨z,t⟩)
    (F.ambientBatchPairs_used_subset P ⟨z,u⟩)

/-- Aggregation is across all actual batches of the parent box, before
any low-path coloring and before routing. -/
def boxPairs (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (z : L.FoldBoxIndex i) :
    OwnedTwoEdgeFamily12 (L.foldDescendantGraph i z)
      (fun r : Fin (L.foldCores i z).length => ((L.foldCores i z).get r).vertices) :=
  OwnedTwoEdgeFamily12.sigma (fun t => F.ambientBatchPairs P ⟨z,t⟩) (F.ambientBatchPairs_disjoint P z)

theorem boxPairs_good (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (z : L.FoldBoxIndex i) (j : (F.boxPairs P z).Index) :
    (F.boxPairs P z).left j∈F.activeVertices z ∧ (F.boxPairs P z).right j∈F.activeVertices z :=
  F.ambientBatchPairs_good P ⟨z,j.1⟩ j.2

/-- The entire aggregated path family is charged to the degree in the
whole original descendant graph, not separately to each batch. -/
theorem boxPairs_endpoint_load (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (z : L.FoldBoxIndex i) (v : V) :
    (endpointLoad (F.boxPairs P z).left (F.boxPairs P z).right v:ℝ) ≤
      routingAllowance (logScale (originalLog V) L.stopIndex i) := by
  by_cases hv : v∈F.activeVertices z
  · have hh := (F.boxPairs P z).certificate.load_le v
    exact (show (endpointLoad (F.boxPairs P z).left (F.boxPairs P z).right v:ℝ) ≤
      (L.foldDescendantGraph i z).degree v by exact_mod_cast hh).trans (F.activeVertices_good z hv)
  · have ha : univ.filter (fun j : (F.boxPairs P z).Index => (F.boxPairs P z).left j=v)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro j _ he
      exact hv (he ▸ (F.boxPairs_good P z j).1)
    have hb : univ.filter (fun j : (F.boxPairs P z).Index => (F.boxPairs P z).right j=v)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro j _ he
      exact hv (he ▸ (F.boxPairs_good P z j).2)
    simp only [endpointLoad,ha,hb,card_empty,zero_add,Nat.cast_zero]
    exact (routingAllowance_pos _).le

def corePairs (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (r : L.FoldCoreIndex i) :
    OwnedTwoEdgeFamily12 (L.foldDescendantGraph i r.1)
      (fun j : Fin (L.foldCores i r.1).length => ((L.foldCores i r.1).get j).vertices) :=
  (F.boxPairs P r.1).restrict (fun j => (F.boxPairs P r.1).owner j=r.2)

theorem corePairs_endpoints (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (j : (F.corePairs P r).Index) :
    (F.corePairs P r).left j∈(L.foldCorePiece i r).vertices ∧
      (F.corePairs P r).right j∈(L.foldCorePiece i r).vertices := by
  have ha := (F.boxPairs P r.1).left_mem j.val
  have hb := (F.boxPairs P r.1).right_mem j.val
  rw [j.property] at ha hb
  exact ⟨ha,hb⟩

end ActualFoldStage12
end
end Cycle12.Even12
