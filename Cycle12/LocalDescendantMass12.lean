import Cycle12.ActualFoldDescendants12
import Cycle12.ActiveFamilyMass12

namespace Cycle12.Even12
open Cycle12.Global12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
open OAI.ErdosGallai.Indexing (GraphBatches)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EvenScaleLayers12.local_frontier_member {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (j k : ℕ) {P Q : AssignedPiece V}
    (hP : P∈advance L.splitter 0 j [originalPiece G]) (hQ : Q∈advance L.splitter j k [P]) :
    Q∈advance L.splitter 0 (j+k) [originalPiece G] := by
  rw [advance_add,Nat.zero_add]
  exact advance_member_of_mem L.splitter j k hP hQ

/-- The same global overlap bound applies to the descendants of each
particular parent, with that parent's order as the normalization. -/
theorem EvenScaleLayers12.local_layer_mass {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {j k : ℕ} (hjk : j+k≤L.stopIndex+3) {P : AssignedPiece V}
    (hP : P∈advance L.splitter 0 j [originalPiece G]) :
    vertexMass (advance L.splitter j k [P])≤M*P.vertices.card := by
  have hb : ∀ t<k,∀ Q∈advance L.splitter j t [P],
      vertexMass (L.splitter (j+t) Q).boxes≤
        (1+overlapAt (originalLog V) L.stopIndex (j+t))*Q.vertices.card := by
    intro t ht Q hQ
    have hmem := L.local_frontier_member j t hP hQ
    have hstage := (L.bounds (j+t) (by omega) Q hmem).2.1
    have hr := (overlap_halfline (logScale_minimum L.initial_log_pos.le L.phase_lower
      (by omega : j+t<L.stopIndex+3))).2
    have hh := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1:ℝ)) hr) (Nat.cast_nonneg Q.vertices.card)
    exact hstage.trans hh
  have hsum : (∑ t∈range k,overlapAt (originalLog V) L.stopIndex (j+t))≤globalOverlapSumUpper := by
    have hh := actual_overlap_prefix L hjk
    rw [Finset.sum_range_add] at hh
    have hn : 0≤∑ t∈range j,overlapAt (originalLog V) L.stopIndex t :=
      sum_nonneg (fun t _ => overlapAt_nonneg _ _ _)
    linarith only [hh,hn]
  have hm := variable_mass_of_overlap_sum L.splitter j k [P]
    (overlapAt (originalLog V) L.stopIndex) (fun t _ => overlapAt_nonneg _ _ _)
    hsum global_overlap_fraction.1 hb
  simp only [vertexMass_cons,vertexMass_nil,add_zero] at hm
  have hh := mul_le_mul_of_nonneg_right global_overlap_fraction.2 (Nat.cast_nonneg P.vertices.card)
  exact hm.trans (by convert hh using 1 <;> ring)

theorem EvenScaleLayers12.descendant_mass_bound {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex) {P : AssignedPiece V}
    (hP : P∈advance L.splitter 0 (i+1) [originalPiece G]) :
    vertexMass (advance L.splitter (i+1) 2 [P])≤M*P.vertices.card :=
  L.local_layer_mass (by omega) hP

end
end Cycle12.Even12

namespace Cycle12
open OAI.ErdosGallai.Indexing
noncomputable section

theorem graphBatches_enlarge_mass {V : Type} {F : SimpleGraph V} {Y : Finset V}
    {B T T' : ℝ} (A : GraphBatches F Y B T) (hB : 0<B) (hT : T≤T') :
    Nonempty (GraphBatches F Y B T') := by
  refine ⟨{A with mass_le := A.mass_le.trans hT,count_le := A.count_le.trans ?_}⟩
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by norm_num : (0:ℝ)≤2)) hB.le
  linarith only [hh]

end
end Cycle12
