import Cycle12.ActualFoldEdges12
import Cycle12.JointFoldRouting12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem disjoint_supported_edge_sets {G H : SimpleGraph V} {U T : Finset V}
    (hG : SupportedOn G U) (hH : SupportedOn H T) (hUT : Disjoint U T) :
    Disjoint G.edgeSet H.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.ind with
  | _ x y => exact Finset.disjoint_left.mp hUT (hG he).1 (hH hf).1

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev EvenScaleLayers12.FoldCoreIndex {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) :=
  (z : L.FoldBoxIndex i) × Fin (L.foldCores i z).length

def EvenScaleLayers12.foldCorePiece {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (r : L.FoldCoreIndex i) : AssignedPiece V := (L.foldCores i r.1).get r.2

theorem EvenScaleLayers12.fold_core_edge_disjoint {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) : Pairwise (fun r t : L.FoldCoreIndex i =>
      Disjoint (L.foldCorePiece i r).graph.edgeSet (L.foldCorePiece i t).graph.edgeSet) := by
  intro r t hrt
  by_cases h : r.1=t.1
  · rcases r with ⟨z,r⟩
    rcases t with ⟨y,t⟩
    dsimp only at h
    subst y
    have hrt' : r ≠ t := by intro he; subst t; exact hrt rfl
    have hd := (L.actual_box_data hi (L.foldParent_mem i z) (L.foldBox_mem i z)).2.1 hrt'
    exact disjoint_supported_edge_sets ((L.foldCores i z).get r).supported
      ((L.foldCores i z).get t).supported hd
  · exact (L.fold_boxes_disjoint i h).mono
      (edgeSet_mono (L.fold_core_le_box i r.1 r.2)) (edgeSet_mono (L.fold_core_le_box i t.1 t.2))

theorem EvenScaleLayers12.fold_core_order_sum {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) :
    (∑ r : L.FoldCoreIndex i,((L.foldCorePiece i r).vertices.card:ℝ))=L.coreMass i := by
  rw [Fintype.sum_sigma,←L.fold_core_mass i]
  apply sum_congr rfl
  intro z hz
  exact list_sum_get _ (fun R : AssignedPiece V => (R.vertices.card:ℝ))

structure AssignedCoreBanks12 (P : AssignedPiece V) (w : ℝ) where
  coloring : Sym2 P.vertices → Bool
  routing : OAI.ErdosGallai.CutExpansion
    (splitBank (P.graph.induce (P.vertices:Set V)) coloring true) (router_bank*(2:ℝ)^(s*w))
  completion : OAI.ErdosGallai.CutExpansion
    (splitBank (P.graph.induce (P.vertices:Set V)) coloring false) (completion_bank*(2:ℝ)^(s*w))
  disjoint : Disjoint (splitBank (P.graph.induce (P.vertices:Set V)) coloring true)
    (splitBank (P.graph.induce (P.vertices:Set V)) coloring false)
  cover : splitBank (P.graph.induce (P.vertices:Set V)) coloring true ⊔
    splitBank (P.graph.induce (P.vertices:Set V)) coloring false=P.graph.induce (P.vertices:Set V)

theorem EvenScaleLayers12.fold_core_local_data {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i) :
    let P := L.foldCorePiece i r
    let w := logScale (originalLog V) L.stopIndex i
    2 ≤ Fintype.card P.vertices ∧
      (Fintype.card P.vertices:ℝ) ≤ (2:ℝ)^(rho*w) ∧
      OAI.ErdosGallai.CutExpansion (P.graph.induce (P.vertices:Set V)) ((1023/1024)*(2:ℝ)^(s*w)) := by
  let P := L.foldCorePiece i r
  let w := logScale (originalLog V) L.stopIndex i
  have hd := (L.actual_box_data hi (L.foldParent_mem i r.1) (L.foldBox_mem i r.1)).2.2.2.1 r.2
  have hlower : (2:ℝ)^(s*logScale (originalLog V) L.stopIndex i) < P.vertices.card := hd.1
  have hexp : CutExpansionOn P.graph P.vertices
      ((1023/1024)*(2:ℝ)^(s*logScale (originalLog V) L.stopIndex i)) := hd.2.2.1
  have hc : Fintype.card P.vertices=P.vertices.card := Fintype.card_coe _
  have hp : (0:ℝ) < P.vertices.card := (rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).trans hd.1
  have hw0 := logScale_minimum L.initial_log_pos.le L.phase_lower (by omega : i < L.stopIndex+3)
  have hlin := (bank_preparation_scale_bounds hw0 hp hd.2.1).1
  refine ⟨?_,?_,?_⟩
  · change 2 ≤ Fintype.card P.vertices
    rw [hc]
    have hh : (2:ℝ) ≤ P.vertices.card := by linarith only [hlin,hlower]
    exact_mod_cast hh
  · change (Fintype.card P.vertices:ℝ) ≤ _
    rw [hc]
    exact hd.2.1
  · change OAI.ErdosGallai.CutExpansion (P.graph.induce (P.vertices:Set V)) _
    convert cutExpansionOn_induce hexp using 1

/-- Every indexed selected core now has its own actual biased edge
banks, prepared before any low, matching, or quotient route is chosen. -/
theorem EvenScaleLayers12.fold_core_banks {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i) :
    Nonempty (AssignedCoreBanks12 (L.foldCorePiece i r) (logScale (originalLog V) L.stopIndex i)) := by
  have hd := L.fold_core_local_data hi r
  obtain ⟨ω,hr,hc,hdisj,hcover⟩ := prepare_even_banks_at_scale
    ((L.foldCorePiece i r).graph.induce ((L.foldCorePiece i r).vertices:Set V)) hd.1
    (logScale_minimum L.initial_log_pos.le L.phase_lower (by omega)) hd.2.1 (by convert hd.2.2 using 1)
  refine ⟨⟨ω,?_,?_,hdisj,hcover⟩⟩
  · convert hr using 1
  · convert hc using 1

end
end Cycle12.Even12
