import Cycle12.FoldTargetGraph12
import Cycle12.TerminalPackingAssembly
import Cycle12.ActualFoldPrefixMass12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

theorem EvenScaleLayers12.foldCore_mem_level (L : EvenScaleLayers12 G) (i : ℕ)
    (r : L.FoldCoreIndex i) :
    L.foldCorePiece i r∈levelPieces L.splitter i (advance L.splitter 0 i [originalPiece G]) := by
  apply List.mem_flatMap.mpr
  refine ⟨L.foldParent i r.1,L.foldParent_mem i r.1,?_⟩
  exact List.mem_flatMap.mpr ⟨L.foldBox i r.1,L.foldBox_mem i r.1,List.get_mem _ r.2⟩

theorem EvenScaleLayers12.level_mem_foldCore (L : EvenScaleLayers12 G) (i : ℕ)
    {R : AssignedPiece V} (hR : R∈levelPieces L.splitter i (advance L.splitter 0 i [originalPiece G])) :
    ∃ r : L.FoldCoreIndex i,L.foldCorePiece i r=R := by
  obtain ⟨A,hA,B,hB,hR⟩ := (by simpa only [levelPieces,List.mem_flatMap] using hR :
    ∃ A∈advance L.splitter 0 i [originalPiece G],∃ B∈(L.splitter i A).boxes,R∈(L.splitter i A).pieces B)
  obtain ⟨a,rfl⟩ := List.mem_iff_get.mp hA
  obtain ⟨b,rfl⟩ := List.mem_iff_get.mp hB
  obtain ⟨r,rfl⟩ := List.mem_iff_get.mp hR
  exact ⟨⟨⟨a,b⟩,r⟩,rfl⟩

theorem EvenScaleLayers12.foldCore_edges_level (L : EvenScaleLayers12 G) (i : ℕ) :
    (⋃ r : L.FoldCoreIndex i,(L.foldCorePiece i r).graph.edgeSet)=
      (graphUnion ((levelPieces L.splitter i (advance L.splitter 0 i [originalPiece G])).map AssignedPiece.graph)).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · intro he
      obtain ⟨r,he⟩ := Set.mem_iUnion.mp he
      exact (graphUnion_adj _ x y).mpr ⟨(L.foldCorePiece i r).graph,
        List.mem_map.mpr ⟨_,L.foldCore_mem_level i r,rfl⟩,he⟩
    · intro he
      obtain ⟨H,hH,hxy⟩ := (graphUnion_adj _ x y).mp he
      obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hH
      obtain ⟨r,rfl⟩ := L.level_mem_foldCore i hR
      exact Set.mem_iUnion.mpr ⟨r,hxy⟩

def EvenScaleLayers12.foldOtherPieces (L : EvenScaleLayers12 G) (i : ℕ) : List (AssignedPiece V) :=
  pastPieces L.splitter 0 i [originalPiece G]++
    levelPieces L.splitter (i+1) (advance L.splitter 0 (i+1) [originalPiece G])++
      levelPieces L.splitter (i+2) (advance L.splitter 0 (i+2) [originalPiece G])

theorem EvenScaleLayers12.foldOther_mem_prefix (L : EvenScaleLayers12 G) (i : ℕ)
    {R : AssignedPiece V} (hR : R∈L.foldOtherPieces i) :
    R∈pastPieces L.splitter 0 (i+3) [originalPiece G] := by
  simp only [foldOtherPieces,pastPieces,List.mem_append,Nat.zero_add] at hR ⊢
  tauto

theorem EvenScaleLayers12.foldOther_mass (L : EvenScaleLayers12 G) (i : ℕ) :
    vertexMass (L.foldOtherPieces i)+L.coreMass i=
      vertexMass (pastPieces L.splitter 0 (i+3) [originalPiece G]) := by
  simp only [foldOtherPieces,pastPieces,vertexMass_append,coreMass,Nat.zero_add]
  ring

theorem EvenScaleLayers12.fold_prefix_mass (L : EvenScaleLayers12 G) {i : ℕ} (hi : i≤L.stopIndex) :
    vertexMass (pastPieces L.splitter 0 (i+3) [originalPiece G])=
      ∑ j : Fin (L.stopIndex+3) with j.val ≤ i+2, L.coreMass j.val := by
  rw [pastPieces_mass]
  simp only [Nat.zero_add]
  change (∑ j∈range (i+3),L.coreMass j)=_
  symm
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    exact mem_range.mpr (by have h := (mem_filter.mp hj).2; omega)
  · intro j hj k hk h
    exact Fin.ext h
  · intro j hj
    have h := mem_range.mp hj
    exact ⟨⟨j,by omega⟩,mem_filter.mpr ⟨mem_univ _,by dsimp; omega⟩,rfl⟩
  · intro j hj
    rfl

theorem EvenScaleLayers12.foldTarget_eq_union (L : EvenScaleLayers12 G) (i : ℕ) :
    L.foldTargetGraph i=graphUnion
      ((levelPieces L.splitter i (advance L.splitter 0 i [originalPiece G])).map AssignedPiece.graph++
        (advance L.splitter 0 (i+3) [originalPiece G]).map AssignedPiece.graph) := by
  apply SimpleGraph.edgeSet_injective
  rw [L.foldTarget_edges i,graphUnion_append,edgeSet_sup,
    L.foldCore_edges_level i,L.fold_descendant_edge_cover i]

/-- Replace the selected layer and the whole frontier together. All
other processed cores and long cycles remain separate original-edge parts. -/
theorem EvenScaleLayers12.fold_replacement_partition (L : EvenScaleLayers12 G) (i : ℕ) :
    GraphPartition G (pastCycles L.splitter 0 (i+3) [originalPiece G]++
      (L.foldOtherPieces i).map AssignedPiece.graph++[L.foldTargetGraph i]) := by
  have hp : GraphPartition G (pastCycles L.splitter 0 (i+3) [originalPiece G]++
      (L.foldOtherPieces i).map AssignedPiece.graph++
        ((levelPieces L.splitter i (advance L.splitter 0 i [originalPiece G])).map AssignedPiece.graph++
          (advance L.splitter 0 (i+3) [originalPiece G]).map AssignedPiece.graph)) := by
    intro x y
    have hh := past_partition L.splitter 0 (i+3) (originalPiece G) x y
    simp only [foldOtherPieces,pastPieces,List.map_append,edgeOccurrences_append,Nat.zero_add,originalPiece] at hh ⊢
    by_cases hxy : G.Adj x y
    · simp only [hxy,ite_true] at hh ⊢
      omega
    · simp only [hxy,ite_false] at hh ⊢
      omega
  rw [L.foldTarget_eq_union i]
  exact partition_merge_remainder hp

theorem EvenScaleLayers12.fold_prefix_assembly (L : EvenScaleLayers12 G) {i : ℕ} (hi : i≤L.stopIndex)
    (ih : PotentialBelow (Fintype.card V)) (T : CyclePacking (L.foldTargetGraph i)) :
    ∃ R : CyclePacking G,R.weight≤
      lossJ (logScale (originalLog V) L.stopIndex i)*Fintype.card V+
        (1+C*eta)*vertexMass (L.foldOtherPieces i)+T.weight := by
  obtain ⟨R,hR⟩ := terminal_packing_assembly _ _ (L.fold_replacement_partition i)
    (pastCycles_good L.splitter 0 (i+3) [originalPiece G])
    (fun P hP => L.past_core_packing (by omega : i+3≤L.stopIndex+3) ih.unweighted
      P (L.foldOther_mem_prefix i hP)) T (le_refl T.weight)
  refine ⟨R,hR.trans ?_⟩
  linarith only [L.fold_long_cycle_payment hi]

end
end Cycle12.Even12
