import Cycle12.ActualFoldStage12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EvenScaleLayers12.fold_box_le_parent {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (z : L.FoldBoxIndex i) : (L.foldBox i z).graph ≤ (L.foldParent i z).graph :=
  partition_member_le (L.splitter i (L.foldParent i z)).partition
    (List.mem_append_right _ (List.mem_map.mpr ⟨_,L.foldBox_mem i z,rfl⟩))

theorem EvenScaleLayers12.fold_child_le_box {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (z : L.FoldBoxIndex i) : (L.foldChild i z).graph ≤ (L.foldBox i z).graph :=
  partition_member_le ((L.splitter i (L.foldParent i z)).box_partition _ (L.foldBox_mem i z))
    (List.mem_cons_self ..)

theorem EvenScaleLayers12.fold_descendant_le_box {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (z : L.FoldBoxIndex i) : L.foldDescendantGraph i z ≤ (L.foldBox i z).graph :=
  (descendant_union_le_original L.splitter (i+1) 2 (L.foldChild i z)).trans (L.fold_child_le_box i z)

theorem EvenScaleLayers12.fold_core_le_box {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (z : L.FoldBoxIndex i) (r : Fin (L.foldCores i z).length) :
    ((L.foldCores i z).get r).graph ≤ (L.foldBox i z).graph :=
  partition_member_le ((L.splitter i (L.foldParent i z)).box_partition _ (L.foldBox_mem i z))
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,List.get_mem _ r,rfl⟩))

/-- Different indexed boxes have disjoint original edge sets, even if
their vertex sets overlap. -/
theorem EvenScaleLayers12.fold_boxes_disjoint {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) : Pairwise (fun z t : L.FoldBoxIndex i =>
      Disjoint (L.foldBox i z).graph.edgeSet (L.foldBox i t).graph.edgeSet) := by
  intro z t hzt
  by_cases hp : z.1=t.1
  · rcases z with ⟨p,r⟩
    rcases t with ⟨q,u⟩
    dsimp only at hp
    subst q
    have hru : r ≠ u := by intro h; subst u; exact hzt rfl
    have hh := graphPartition_pairwise
      (L.splitter i ((advance L.splitter 0 i [originalPiece G]).get p)).partition
    have hb := (List.pairwise_append.mp hh).2.1
    exact list_pairwise_get (List.pairwise_map.mp hb) (fun _ _ h => h.symm) hru
  · have hd := (indexed_assigned_edges (advance L.splitter 0 i [originalPiece G])
      (advance_frontier_partition L.splitter 0 i (originalPiece G))).1 hp
    exact hd.mono (edgeSet_mono (L.fold_box_le_parent i z)) (edgeSet_mono (L.fold_box_le_parent i t))

theorem EvenScaleLayers12.fold_descendants_disjoint {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) : Pairwise (fun z t : L.FoldBoxIndex i =>
      Disjoint (L.foldDescendantGraph i z).edgeSet (L.foldDescendantGraph i t).edgeSet) := by
  intro z t hzt
  exact (L.fold_boxes_disjoint i hzt).mono
    (edgeSet_mono (L.fold_descendant_le_box i z)) (edgeSet_mono (L.fold_descendant_le_box i t))

theorem EvenScaleLayers12.foldChild_mem {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (z : L.FoldBoxIndex i) :
    L.foldChild i z∈advance L.splitter 0 (i+1) [originalPiece G] := by
  rw [advance_succ,Nat.zero_add]
  exact (nextLayer_mem L.splitter i _ _).mpr
    ⟨L.foldParent i z,L.foldParent_mem i z,L.foldBox i z,L.foldBox_mem i z,rfl,rfl⟩

theorem EvenScaleLayers12.foldChild_cover {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) {Q : AssignedPiece V} (hQ : Q∈advance L.splitter 0 (i+1) [originalPiece G]) :
    ∃ z : L.FoldBoxIndex i,Q=L.foldChild i z := by
  rw [advance_succ,Nat.zero_add] at hQ
  obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem L.splitter i _ Q).mp hQ
  obtain ⟨p,rfl⟩ := List.mem_iff_get.mp hP
  obtain ⟨r,rfl⟩ := List.mem_iff_get.mp hB
  refine ⟨⟨p,r⟩,?_⟩
  cases Q
  dsimp only at hv hg
  subst_vars
  rfl

theorem EvenScaleLayers12.foldDescendants_cover {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (Q : AssignedPiece V) :
    (∃ z : L.FoldBoxIndex i,Q∈L.foldDescendants i z) ↔
      Q∈advance L.splitter 0 (i+3) [originalPiece G] := by
  constructor
  · rintro ⟨z,hz⟩
    have hh := L.local_frontier_member (i+1) 2 (L.foldChild_mem i z) hz
    simpa only [Nat.add_assoc] using hh
  · intro hQ
    rw [show i+3=(i+1)+2 by omega,advance_add,Nat.zero_add,
      advance_singleton_flatMap L.splitter (i+1) 2] at hQ
    obtain ⟨R,hR,hQ⟩ := List.mem_flatMap.mp hQ
    obtain ⟨z,rfl⟩ := L.foldChild_cover i hR
    exact ⟨z,hQ⟩

theorem EvenScaleLayers12.fold_descendant_edge_cover {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) : (⋃ z : L.FoldBoxIndex i,(L.foldDescendantGraph i z).edgeSet)=
      (graphUnion ((advance L.splitter 0 (i+3) [originalPiece G]).map AssignedPiece.graph)).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet,foldDescendantGraph,graphUnion_adj,List.mem_map]
    constructor
    · rintro ⟨z,H,⟨Q,hQ,rfl⟩,hxy⟩
      exact ⟨Q.graph,⟨Q,(L.foldDescendants_cover i Q).mp ⟨z,hQ⟩,rfl⟩,hxy⟩
    · rintro ⟨H,⟨Q,hQ,rfl⟩,hxy⟩
      obtain ⟨z,hz⟩ := (L.foldDescendants_cover i Q).mpr hQ
      exact ⟨z,Q.graph,⟨Q,hz,rfl⟩,hxy⟩

/-- No selected router core uses any original descendant edge, including
descendants attached to other boxes. -/
theorem EvenScaleLayers12.fold_core_descendants_disjoint {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) (z t : L.FoldBoxIndex i)
    (r : Fin (L.foldCores i z).length) :
    Disjoint ((L.foldCores i z).get r).graph.edgeSet (L.foldDescendantGraph i t).edgeSet := by
  by_cases hzt : z=t
  · subst t
    exact (L.actual_box_data hi (L.foldParent_mem i z) (L.foldBox_mem i z)).2.2.2.2 r
  · exact (L.fold_boxes_disjoint i hzt).mono
      (edgeSet_mono (L.fold_core_le_box i z r)) (edgeSet_mono (L.fold_descendant_le_box i t))

namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

def batchGraph (F : ActualFoldStage12 L i) (t : F.BatchIndex) : SimpleGraph V :=
  (F.batches t.1).graph t.2

theorem batch_graph_disjoint (F : ActualFoldStage12 L i) :
    Pairwise (fun t u : F.BatchIndex => Disjoint (F.batchGraph t).edgeSet (F.batchGraph u).edgeSet) := by
  intro t u htu
  by_cases h : t.1=u.1
  · rcases t with ⟨z,t⟩
    rcases u with ⟨q,u⟩
    dsimp only at h
    subst q
    exact (F.batches z).disjoint (by intro he; change t=u at he; subst u; exact htu rfl)
  · exact (L.fold_descendants_disjoint i h).mono
      (edgeSet_mono ((F.batches t.1).graph_le t.2)) (edgeSet_mono ((F.batches u.1).graph_le u.2))

theorem batch_graph_cover (F : ActualFoldStage12 L i) :
    (⋃ t : F.BatchIndex,(F.batchGraph t).edgeSet)=
      (graphUnion ((advance L.splitter 0 (i+3) [originalPiece G]).map AssignedPiece.graph)).edgeSet := by
  rw [←L.fold_descendant_edge_cover i]
  simp only [batchGraph]
  rw [Set.iUnion_sigma]
  congr 1
  funext z
  exact (F.batches z).edge_cover

end ActualFoldStage12
end
end Cycle12.Even12
