import Cycle12.ActualActiveBatches12
import Cycle12.EvenCorePacking12

namespace Cycle12
open SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def actualBoxRemainder {P : AssignedPiece V} (s : StageSplit P)
    (B : AssignedPiece V) (hB : B∈s.boxes) : AssignedPiece V :=
  ⟨B.vertices,s.remainder B,s.remainder_supported B hB⟩

theorem descendant_union_le_original (s : SplitSystem V) (j k : ℕ) (P : AssignedPiece V) :
    graphUnion ((advance s j k [P]).map AssignedPiece.graph) ≤ P.graph := by
  apply graphUnion_le_of_members
  intro H hH
  exact partition_member_le (past_partition s j k P) (List.mem_append_right _ hH)

theorem actual_box_core_remainder_disjoint {P : AssignedPiece V} (s : StageSplit P)
    {B R : AssignedPiece V} (hB : B∈s.boxes) (hR : R∈s.pieces B) :
    Disjoint R.graph.edgeSet (s.remainder B).edgeSet := by
  have hh := (List.pairwise_cons.mp (graphPartition_pairwise (s.box_partition B hB))).1
    R.graph (List.mem_map.mpr ⟨R,hR,rfl⟩)
  exact hh.symm

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
open OAI.ErdosGallai.Indexing (GraphBatches ActiveFamily)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The selected stage box supplies its actual disjoint core family and
its actual child remainder; descendants remain disjoint from every core. -/
theorem EvenScaleLayers12.actual_box_data {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) {P B : AssignedPiece V}
    (hP : P∈advance L.splitter 0 i [originalPiece G]) (hB : B∈(L.splitter i P).boxes) :
    let child := actualBoxRemainder (L.splitter i P) B hB
    let cores := (L.splitter i P).pieces B
    let w := logScale (originalLog V) L.stopIndex i
    let F := graphUnion ((advance L.splitter (i+1) 2 [child]).map AssignedPiece.graph)
    child∈advance L.splitter 0 (i+1) [originalPiece G] ∧
      Pairwise (fun r t : Fin cores.length => Disjoint (cores.get r).vertices (cores.get t).vertices) ∧
      (∀ r : Fin cores.length,(cores.get r).vertices⊆B.vertices) ∧
      (∀ r : Fin cores.length,(2:ℝ)^(s*w)<(cores.get r).vertices.card ∧
        ((cores.get r).vertices.card:ℝ) ≤ (2:ℝ)^(rho*w) ∧
        CutExpansionOn (cores.get r).graph (cores.get r).vertices ((1023/1024)*(2:ℝ)^(s*w)) ∧
        (∀ v,Even ((cores.get r).graph.degree v))) ∧
      (∀ r : Fin cores.length,Disjoint (cores.get r).graph.edgeSet F.edgeSet) := by
  dsimp only
  have hchild : actualBoxRemainder (L.splitter i P) B hB∈
      advance L.splitter 0 (i+1) [originalPiece G] := by
    rw [advance_succ,Nat.zero_add]
    exact (nextLayer_mem L.splitter i _ _).mpr ⟨P,hP,B,hB,rfl,rfl⟩
  have hbounds := L.bounds i (by omega) P hP
  refine ⟨hchild,?_,?_,?_,?_⟩
  · exact list_pairwise_get ((L.splitter i P).piece_disjoint B hB) (fun _ _ h => h.symm)
  · intro r
    exact (L.splitter i P).piece_subset B hB _ (List.get_mem _ r)
  · intro r
    exact hbounds.2.2.2.1 B hB _ (List.get_mem _ r)
  · intro r
    have hd := actual_box_core_remainder_disjoint (L.splitter i P) hB (List.get_mem _ r)
    exact hd.mono_right (edgeSet_mono (descendant_union_le_original L.splitter (i+1) 2
      (actualBoxRemainder (L.splitter i P) B hB)))

/-- Instantiate descendant batching and active sets with these actual
selected cores, retaining injective router ownership and exact mass loss. -/
theorem EvenScaleLayers12.actual_box_active_families {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) {P B : AssignedPiece V}
    (hP : P∈advance L.splitter 0 i [originalPiece G]) (hB : B∈(L.splitter i P).boxes) :
    let child := actualBoxRemainder (L.splitter i P) B hB
    let cores := (L.splitter i P).pieces B
    let U := fun r : Fin cores.length => (cores.get r).vertices
    let w := logScale (originalLog V) L.stopIndex i
    let F := graphUnion ((advance L.splitter (i+1) 2 [child]).map AssignedPiece.graph)
    ∃ batches : GraphBatches F B.vertices ((2:ℝ)^(b*w)) (M*B.vertices.card),
      ∃ A : ActiveFamily F B.vertices batches.vertices U ((2:ℝ)^(alpha*w)) ((2:ℝ)^(lam*w)),
        (∀ t,Function.Injective (A.router t)) ∧
        (∑ r,((U r).card:ℝ))-
          (entropyRemainder12 (q0*w)*M*B.vertices.card)/(2:ℝ)^(alpha*w)-
          (2:ℝ)^(lam*w)*(1+2*(M*B.vertices.card)/(2:ℝ)^(b*w))*
            ((B.vertices.card:ℝ)/(2:ℝ)^(s*w)) ≤
          ∑ t,∑ j,((A.vertices t j).card:ℝ) ∧
        (∑ t,∑ j,((A.vertices t j).card:ℝ))+B.vertices.card ≤
          (∑ r,((U r).card:ℝ))+M*B.vertices.card := by
  dsimp only
  have hdata := L.actual_box_data hi hP hB
  exact L.prepare_active_descendants hi hdata.1 _ hdata.2.1 hdata.2.2.1
    (fun r => (hdata.2.2.2.1 r).1.le)

end
end Cycle12.Even12
