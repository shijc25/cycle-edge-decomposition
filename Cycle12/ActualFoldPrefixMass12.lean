import Cycle12.ExactActiveBatches12
import Cycle12.EvenLayerCyclePayment12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EvenScaleLayers12.processed_log_lower {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {j : ℕ} (hj : j < L.stopIndex+3) :
    theta2^j*originalLog V ≤ logScale (originalLog V) L.stopIndex j := by
  unfold logScale
  by_cases h : j ≤ L.stopIndex+1
  · rw [three_rate_regular _ _ _ _ h]
  · have he : j=L.stopIndex+2 := by omega
    subst j
    rw [three_rate_penultimate,show L.stopIndex+2=(L.stopIndex+1)+1 by omega,pow_succ]
    have hh := mul_le_mul_of_nonneg_right (show theta2 ≤ theta1 by norm_num [theta2,theta1])
      (mul_nonneg (pow_nonneg (show 0 ≤ theta2 by norm_num [theta2]) (L.stopIndex+1)) L.initial_log_pos.le)
    nlinarith only [hh]

/-- The prefix ending two stages after the chosen core layer is paid
at that layer's actual scale, including the last possible active layer. -/
theorem EvenScaleLayers12.fold_prefix_series {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) {d : ℝ} (hd : 0 < d) :
    (∑ j∈range (i+3),(2:ℝ)^(-d*logScale (originalLog V) L.stopIndex j)) ≤
      scaleMassSeries theta2 (d*theta2^2*logScale (originalLog V) L.stopIndex i) := by
  have hw : 0 < logScale (originalLog V) L.stopIndex i :=
    (show 0 < wA by norm_num [wA]).trans_le (logScale_active L.initial_log_pos.le L.phase_lower hi)
  have hs := geometric_scale_sum_bound (show 0 < theta2 by norm_num [theta2])
    (show theta2 < 1 by norm_num [theta2])
    (mul_pos (pow_pos (show 0 < theta2 by norm_num [theta2]) 2) hw) hd (i+2)
    (show theta2^2*logScale (originalLog V) L.stopIndex i ≤ theta2^(i+2)*originalLog V by
      unfold logScale
      rw [three_rate_regular _ _ _ _ (by omega),pow_add]
      nlinarith)
  have hh : (∑ j∈range (i+3),(2:ℝ)^(-d*logScale (originalLog V) L.stopIndex j)) ≤
      ∑ j∈range (i+3),(2:ℝ)^(-d*(theta2^j*originalLog V)) := by
    apply sum_le_sum
    intro j hj
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left (L.processed_log_lower (j:=j)
      (by have := mem_range.mp hj; omega)) hd.le)
  exact hh.trans (by simpa only [Nat.add_assoc,mul_assoc] using hs)

theorem EvenScaleLayers12.layer_mass_increment {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {j : ℕ} (hj : j < L.stopIndex+3) :
    vertexMass (advance L.splitter 0 (j+1) [originalPiece G]) ≤
      vertexMass (advance L.splitter 0 j [originalPiece G])+
        overlapAt (originalLog V) L.stopIndex j*M*Fintype.card V := by
  have hb : ∀ P∈advance L.splitter 0 j [originalPiece G],
      vertexMass (L.splitter j P).boxes ≤
        (1+overlapAt (originalLog V) L.stopIndex j)*P.vertices.card := by
    intro P hP
    have hstage := (L.bounds j hj P hP).2.1
    have hr := (overlap_halfline (logScale_minimum L.initial_log_pos.le L.phase_lower hj)).2
    exact hstage.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl (1:ℝ)) hr) (Nat.cast_nonneg _))
  have hh := variable_nextLayer_mass L.splitter j _ hb
  have hm := mul_le_mul_of_nonneg_left (actual_layer_mass L (i:=j) (by omega))
    (overlapAt_nonneg (originalLog V) L.stopIndex j)
  rw [advance_succ,Nat.zero_add]
  nlinarith only [hh,hm]

theorem EvenScaleLayers12.layer_mass_additive {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {j : ℕ} (hj : j ≤ L.stopIndex+3) :
    vertexMass (advance L.splitter 0 j [originalPiece G]) ≤
      Fintype.card V+M*(Fintype.card V:ℝ)*
        ∑ t∈range j,overlapAt (originalLog V) L.stopIndex t := by
  induction j with
  | zero => simp [originalPiece]
  | succ j ih =>
    have hp := ih (by omega)
    have hn := L.layer_mass_increment (j:=j) (by omega)
    rw [sum_range_succ]
    nlinarith only [hp,hn]

theorem EvenScaleLayers12.fold_frontier_mass {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) :
    vertexMass (advance L.splitter 0 (i+3) [originalPiece G]) ≤
      (1+lossO (logScale (originalLog V) L.stopIndex i))*Fintype.card V := by
  have hs := mul_le_mul_of_nonneg_left (L.fold_prefix_series hi (show 0 < delta by norm_num [delta]))
    (show 0 ≤ overlap by norm_num [overlap])
  have hm := L.layer_mass_additive (j:=i+3) (by omega)
  simp only [overlapAt,←mul_sum] at hm
  have hh := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (show 0 ≤ M by norm_num [M]) (Nat.cast_nonneg (Fintype.card V)))
  unfold lossO
  nlinarith only [hm,hh]

theorem EvenScaleLayers12.frontier_mass_lower {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) : (Fintype.card V:ℝ) ≤ vertexMass (advance L.splitter 0 i [originalPiece G]) := by
  simpa only [originalPiece,card_univ] using advance_mass_lower L.splitter 0 i (originalPiece G)

theorem EvenScaleLayers12.fold_long_cycle_payment {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) :
    ((pastCycles L.splitter 0 (i+3) [originalPiece G]).length:ℝ) ≤
      lossJ (logScale (originalLog V) L.stopIndex i)*Fintype.card V := by
  let d := scaleData (originalLog V) L.stopIndex L.initial_log_pos.le L.phase_lower
  have hc := even_past_cycles_payment d L.splitter 0 (i+3) [originalPiece G]
    (fun j hj => by change 0+j < L.stopIndex+3; omega)
    (fun j _ => rpow_nonneg (by norm_num) _)
    (fun j hj => by simpa only [d,scaleData,Nat.zero_add] using L.bounds j (by omega))
    (fun j hj => actual_layer_mass L (i:=j) (by omega))
  have he : (∑ j∈range (i+3),d.degree (0+j)/(2*d.cycleLength (0+j)))=
      (∑ j∈range (i+3),(2:ℝ)^(-eps*logScale (originalLog V) L.stopIndex j))/2 := by
    rw [sum_div]
    apply sum_congr rfl
    intro j hj
    simp only [d,scaleData,Nat.zero_add]
    exact power_cycle_charge eps _
  rw [he] at hc
  have hs := div_le_div_of_nonneg_right (L.fold_prefix_series hi (show 0 < eps by norm_num [eps]))
    (show 0 ≤ (2:ℝ) by norm_num)
  have hh := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (show 0 ≤ M by norm_num [M]) (Nat.cast_nonneg (Fintype.card V)))
  exact hc.trans (by convert hh using 1 <;> unfold lossJ <;> ring)

end
end Cycle12.Even12
