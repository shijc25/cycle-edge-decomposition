import Cycle12.PhaseLayerMass12
import Cycle12.EvenActualLayerMass12

namespace Cycle12.Even12
open Cycle12.Global12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem normal_overlap_sum {G : SimpleGraph V} (L : EvenScaleLayers12 G) {j : ℕ}
    (hj : j≤L.stopIndex+1) {A : ℝ} (hA : 0<A) (hphase : A≤theta2^j*originalLog V) :
    (∑ i∈Finset.range (j+1), overlapAt (originalLog V) L.stopIndex i) ≤
      overlap*scaleMassSeries theta2 (delta*A) := by
  have hh := geometric_scale_sum_bound (by norm_num [theta2]) (by norm_num [theta2])
    hA (show 0<delta by norm_num [delta]) j hphase
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num [overlap] : 0≤overlap)
  have he : (∑ i∈Finset.range (j+1), overlapAt (originalLog V) L.stopIndex i) =
      overlap*∑ i∈Finset.range (j+1), (2:ℝ)^(-delta*(theta2^i*originalLog V)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold overlapAt logScale
    rw [three_rate_regular _ _ _ _ (by have := Finset.mem_range.mp hi; omega)]
  rw [he]
  exact hm

theorem phase_layer_mass3 {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {A : ℝ} (hA : 0<A) (hphase : A≤theta2^L.stopIndex*originalLog V)
    (hZ : phaseOverlap3 A<1) {i : ℕ} (hi : i≤L.stopIndex+1) :
    vertexMass (advance L.splitter 0 i [originalPiece G]) ≤ phaseMass3 A*Fintype.card V := by
  have hsum := normal_overlap_sum L (j:=L.stopIndex) (by omega) hA hphase
  have hprefix : (∑ j∈Finset.range i, overlapAt (originalLog V) L.stopIndex j) ≤ phaseOverlap3 A :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
      (fun j _ _ => overlapAt_nonneg _ _ _)).trans hsum
  have hh := actual_layer_mass_of_sum L (by omega) hprefix hZ
  exact hh.trans_eq (by unfold phaseMass3; ring)

theorem phase_layer_mass2 {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {A : ℝ} (hA : 0<A) (hphase : A≤theta2^L.stopIndex*originalLog V)
    (hZ : phaseOverlap2 A<1) {i : ℕ} (hi : i≤L.stopIndex+2) :
    vertexMass (advance L.splitter 0 i [originalPiece G]) ≤ phaseMass2 A*Fintype.card V := by
  have ht : 0<theta2 := by norm_num [theta2]
  have hnext : theta2*A≤theta2^(L.stopIndex+1)*originalLog V := by
    have hh := mul_le_mul_of_nonneg_left hphase ht.le
    rw [pow_succ]
    nlinarith only [hh]
  have hsum := normal_overlap_sum L le_rfl (mul_pos ht hA) hnext
  have hprefix : (∑ j∈Finset.range i, overlapAt (originalLog V) L.stopIndex j) ≤ phaseOverlap2 A := by
    have hfull : (∑ j∈Finset.range (L.stopIndex+2), overlapAt (originalLog V) L.stopIndex j) ≤ phaseOverlap2 A := hsum
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
      (fun j _ _ => overlapAt_nonneg _ _ _)).trans hfull
  have hh := actual_layer_mass_of_sum L (by omega) hprefix hZ
  exact hh.trans_eq (by unfold phaseMass2; ring)

theorem phase_layer_mass1 {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {A : ℝ} (hA : 0<A) (hphase : A≤theta2^L.stopIndex*originalLog V)
    (hZ : phaseOverlap1 A<1) {i : ℕ} (hi : i≤L.stopIndex+3) :
    vertexMass (advance L.splitter 0 i [originalPiece G]) ≤ phaseMass1 A*Fintype.card V := by
  have hh := three_rate_scale_sum_bound (theta0:=theta0) (theta1:=theta1) (theta2:=theta2)
    (delta:=delta) (by norm_num [theta1]) (by norm_num [theta2]) (by norm_num [theta2])
    hA (by norm_num [delta]) L.stopIndex hphase
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num [overlap] : 0≤overlap)
  have hfull : (∑ j∈Finset.range (L.stopIndex+3), overlapAt (originalLog V) L.stopIndex j) ≤ phaseOverlap1 A := by
    simpa only [overlapAt,logScale,←Finset.mul_sum,phaseOverlap1] using hm
  have hprefix : (∑ j∈Finset.range i, overlapAt (originalLog V) L.stopIndex j) ≤ phaseOverlap1 A :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
      (fun j _ _ => overlapAt_nonneg _ _ _)).trans hfull
  have hmass := actual_layer_mass_of_sum L hi hprefix hZ
  exact hmass.trans_eq (by unfold phaseMass1; ring)

theorem actual_piece_mass {G : SimpleGraph V} (L : EvenScaleLayers12 G) {i : ℕ}
    (hi : i<L.stopIndex+3) :
    vertexMass (levelPieces L.splitter i (advance L.splitter 0 i [originalPiece G])) ≤ M*Fintype.card V := by
  have hh := levelPieces_mass L.splitter i (advance L.splitter 0 i [originalPiece G])
  have hm := actual_layer_mass L (i:=i+1) (by omega)
  simp only [advance_succ,Nat.zero_add] at hm
  exact hh.trans hm

end
end Cycle12.Even12
