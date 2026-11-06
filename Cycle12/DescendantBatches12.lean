import Cycle12.AssignedPackingAssembly
import OAI.Combinatorics.CycleDecomposition.BatchIndexing

namespace Cycle12
open SimpleGraph Finset
open OAI.ErdosGallai.Scale
open OAI.ErdosGallai.Indexing (GraphBatches materialize_batches)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem indexed_assigned_edges (L : List (AssignedPiece V))
    (hp : GraphPartition (graphUnion (L.map AssignedPiece.graph)) (L.map AssignedPiece.graph)) :
    Pairwise (fun i j : Fin L.length => Disjoint (L.get i).graph.edgeSet (L.get j).graph.edgeSet) ∧
      (⋃ i : Fin L.length,(L.get i).graph.edgeSet)=
        (graphUnion (L.map AssignedPiece.graph)).edgeSet := by
  constructor
  · exact list_pairwise_get (List.pairwise_map.mp (graphPartition_pairwise hp))
      (fun _ _ h => h.symm)
  · ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet,graphUnion_adj,List.mem_map]
      constructor
      · rintro ⟨i,hi⟩
        exact ⟨(L.get i).graph,⟨L.get i,L.get_mem i,rfl⟩,hi⟩
      · rintro ⟨_,⟨P,hP,rfl⟩,hPxy⟩
        obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hP
        exact ⟨i,hPxy⟩

/-- Materialize actual graphs from the indexed descendant list. The vertex
cover retains isolated vertices, even when all descendant edge sets are empty. -/
theorem assigned_list_batches (L : List (AssignedPiece V)) (Y : Finset V)
    (hp : GraphPartition (graphUnion (L.map AssignedPiece.graph)) (L.map AssignedPiece.graph))
    (hsub : ∀ P∈L,P.vertices⊆Y) (hcover : ∀ v∈Y,∃ P∈L,v∈P.vertices)
    {B : ℝ} (hB : 0<B) (hsmall : ∀ P∈L,(P.vertices.card:ℝ)≤B/2) :
    Nonempty (GraphBatches (graphUnion (L.map AssignedPiece.graph)) Y B (vertexMass L)) := by
  have he := indexed_assigned_edges L hp
  have hY : Y⊆univ.biUnion (fun i : Fin L.length => (L.get i).vertices) := by
    intro v hv
    obtain ⟨P,hP,hvP⟩ := hcover v hv
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hP
    exact mem_biUnion.mpr ⟨i,mem_univ _,hvP⟩
  have hh := materialize_batches (graphUnion (L.map AssignedPiece.graph)) Y
    (fun i : Fin L.length => (L.get i).graph) (fun i => (L.get i).vertices)
    he.1 he.2 (fun i => (L.get i).supported) (fun i => hsub _ (L.get_mem i))
    (by convert hY using 1; ext v; simp only [mem_biUnion]) B hB
    (fun i => hsmall _ (L.get_mem i))
  have hm : (∑ i : Fin L.length,((L.get i).vertices.card:ℝ))=vertexMass L :=
    list_sum_get L (fun P => (P.vertices.card:ℝ))
  rwa [hm] at hh

theorem advance_member_of_mem (s : SplitSystem V) (j k : ℕ)
    {L : List (AssignedPiece V)} {P Q : AssignedPiece V} (hP : P∈L)
    (hQ : Q∈advance s j k [P]) : Q∈advance s j k L := by
  induction k generalizing Q with
  | zero =>
    obtain rfl := List.mem_singleton.mp hQ
    exact hP
  | succ k ih =>
    obtain ⟨R,hR,B,hB,hv,hg⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    exact (nextLayer_mem s (j+k) _ Q).mpr ⟨R,ih hR,B,hB,hv,hg⟩

theorem advance_frontier_partition (s : SplitSystem V) (j k : ℕ) (P : AssignedPiece V) :
    GraphPartition (graphUnion ((advance s j k [P]).map AssignedPiece.graph))
      ((advance s j k [P]).map AssignedPiece.graph) := by
  exact partition_segment (A:=pastCycles s j k [P]++(pastPieces s j k [P]).map AssignedPiece.graph)
    (C:=[]) (by simpa only [List.append_nil] using past_partition s j k P)

/-- Descendants of a particular parent produce disjoint actual batches,
with the exact descendant mass as their common mass/count budget. -/
theorem descendant_batches (s : SplitSystem V) (j k : ℕ) (P : AssignedPiece V)
    {B : ℝ} (hB : 0<B)
    (hsmall : ∀ Q∈advance s j k [P],(Q.vertices.card:ℝ)≤B/2) :
    Nonempty (GraphBatches (graphUnion ((advance s j k [P]).map AssignedPiece.graph))
      P.vertices B (vertexMass (advance s j k [P]))) := by
  exact assigned_list_batches _ _ (advance_frontier_partition s j k P)
    (advance_subset s j k [P] P.vertices (fun Q hQ => by
      obtain rfl := List.mem_singleton.mp hQ; exact subset_rfl))
    (fun v hv => advance_cover s j k [P] P (by simp) v hv) hB hsmall

end
end Cycle12
