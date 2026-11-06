import Cycle12.ActualScaleLayers12
import Cycle12.GlobalMassSeries12

namespace Cycle12.Global12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem ScaleLayers12.initial_log_pos {G : SimpleGraph V} (L : ScaleLayers12 G) :
    0<originalLog V := by
  have ha : 0<wA := by norm_num [wA]
  have hp : 0≤theta2^L.stopIndex := pow_nonneg (by norm_num [theta2]) _
  by_contra h
  have hh := mul_nonpos_of_nonneg_of_nonpos hp (le_of_not_gt h)
  linarith only [L.phase_lower,ha,hh]

def overlapAt (X : ℝ) (k i : ℕ) : ℝ := overlap*(2:ℝ)^(-delta*logScale X k i)

theorem overlapAt_nonneg (X : ℝ) (k i : ℕ) : 0≤overlapAt X k i := by
  exact mul_nonneg (by norm_num [overlap]) (Real.rpow_nonneg (by norm_num) _)

theorem actual_overlap_sum {G : SimpleGraph V} (L : ScaleLayers12 G) :
    (∑ i∈Finset.range (L.stopIndex+3), overlapAt (originalLog V) L.stopIndex i) ≤
      globalOverlapSumUpper := by
  have hh := three_rate_scale_sum_bound (theta0:=theta0) (theta1:=theta1) (theta2:=theta2)
    (delta:=delta) (by norm_num [theta1]) (by norm_num [theta2]) (by norm_num [theta2])
    (by norm_num [wA]) (by norm_num [delta]) L.stopIndex L.phase_lower
  have he1 : theta1*theta2*wA=w0 := by norm_num [theta1,theta2,wA,w0]
  have he2 : delta*(theta2*wA)=delta*w0/theta1 := by norm_num [delta,theta1,theta2,wA,w0]
  rw [he1,he2] at hh
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num [overlap] : 0≤overlap)
  simp only [overlapAt,logScale,←Finset.mul_sum]
  exact hm.trans global_overlap_series_bound

theorem actual_overlap_prefix {G : SimpleGraph V} (L : ScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex+3) :
    (∑ j∈Finset.range i, overlapAt (originalLog V) L.stopIndex j) ≤ globalOverlapSumUpper := by
  apply le_trans _ (actual_overlap_sum L)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
    (fun j _ _ => overlapAt_nonneg _ _ j)

theorem actual_layer_mass_of_sum {G : SimpleGraph V} (L : ScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex+3) {Z : ℝ}
    (hsum0 : (∑ j∈Finset.range i, overlapAt (originalLog V) L.stopIndex j) ≤ Z)
    (hZ : Z<1) :
    vertexMass (advance L.splitter 0 i [originalPiece G]) ≤ (Fintype.card V:ℝ)/(1-Z) := by
  have hb : ∀ j < i, ∀ P∈advance L.splitter 0 j [originalPiece G],
      vertexMass (L.splitter (0+j) P).boxes ≤
        (1+overlapAt (originalLog V) L.stopIndex (0+j))*P.vertices.card := by
    intro j hj P hP
    have hstage := (L.bounds j (by omega) P hP).2.1
    have hr := (overlap_halfline (logScale_minimum L.initial_log_pos.le L.phase_lower (by omega : j<L.stopIndex+3))).2
    have hm := mul_le_mul_of_nonneg_right (add_le_add_left hr 1) (Nat.cast_nonneg (α:=ℝ) P.vertices.card)
    simp only [Nat.zero_add]
    apply hstage.trans
    unfold overlapAt
    nlinarith only [hm]
  have hsum : (∑ j∈Finset.range i, overlapAt (originalLog V) L.stopIndex (0+j)) ≤ Z := by
    simpa only [Nat.zero_add] using hsum0
  have hm := variable_mass_of_overlap_sum L.splitter 0 i [originalPiece G]
    (overlapAt (originalLog V) L.stopIndex) (fun j _ => overlapAt_nonneg _ _ _)
    hsum hZ hb
  simp only [vertexMass_cons,vertexMass_nil,add_zero,originalPiece,Finset.card_univ] at hm
  exact hm

theorem actual_layer_mass {G : SimpleGraph V} (L : ScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex+3) :
    vertexMass (advance L.splitter 0 i [originalPiece G]) ≤ M*Fintype.card V := by
  have hm := actual_layer_mass_of_sum L hi (actual_overlap_prefix L hi) global_overlap_fraction.1
  have hpay := mul_le_mul_of_nonneg_right global_overlap_fraction.2
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  exact hm.trans (by convert hpay using 1 <;> ring)

end
end Cycle12.Global12
