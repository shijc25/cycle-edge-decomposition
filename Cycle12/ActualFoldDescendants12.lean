import Cycle12.DescendantBatches12
import Cycle12.EvenActualLayerMass12

namespace Cycle12.Global12
open Real
noncomputable section

def entropyRemainder12 (w : ℝ) : ℝ :=
  (2:ℝ)^(s*w)*((1001/1000:ℝ)+(rho-s)*w)

theorem entropyRemainder12_nonneg {w : ℝ} (hw : 0≤w) : 0≤entropyRemainder12 w := by
  unfold entropyRemainder12
  apply mul_nonneg (rpow_nonneg (by norm_num) _)
  have hh := mul_nonneg (show 0≤rho-s by norm_num [rho,s]) hw
  linarith only [hh]

theorem entropyRemainder12_monotone : MonotoneOn entropyRemainder12 (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold entropyRemainder12
  apply mul_le_mul
  · exact rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hxy (by norm_num [s]))
  · have hh := mul_le_mul_of_nonneg_left hxy (show 0≤rho-s by norm_num [rho,s])
    linarith only [hh]
  · have hh := mul_nonneg (show 0≤rho-s by norm_num [rho,s]) hx
    linarith only [hh]
  · exact rpow_nonneg (by norm_num) _

theorem descendant_half_batch {w : ℝ} (hw : wA≤w) :
    (2:ℝ)^(rho*(q0*w))≤(2:ℝ)^(b*w)/2 := by
  have hh := mul_le_mul_of_nonneg_left hw (show 0≤b-rho*q0 by
    norm_num [b,rho,q0,theta1,theta2])
  have hb : 1≤(b-rho*q0)*wA := by norm_num [b,rho,q0,theta1,theta2,wA]
  have he : (2:ℝ)^(b*w)/2=(2:ℝ)^(b*w-1) := by
    rw [rpow_sub (by norm_num : (0:ℝ)<2)]
    simp only [rpow_one]
  rw [he]
  apply rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith only [hh,hb]

end
end Cycle12.Global12

namespace Cycle12.Even12
open Cycle12.Global12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
open OAI.ErdosGallai.Indexing (GraphBatches)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EvenScaleLayers12.frontier_order_entropy {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {j : ℕ} (hj : j<L.stopIndex+3) {Q : AssignedPiece V}
    (hQ : Q∈advance L.splitter 0 (j+1) [originalPiece G]) :
    (Q.vertices.card:ℝ)≤(2:ℝ)^(rho*logScale (originalLog V) L.stopIndex j) ∧
    2*(edgeCount Q.graph:ℝ)≤entropyRemainder12 (logScale (originalLog V) L.stopIndex j)*
      Q.vertices.card := by
  obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem L.splitter j _ Q).mp
    (by simpa only [advance_succ,Nat.zero_add] using hQ)
  have hb := L.bounds j hj P hP
  rw [hv,hg]
  refine ⟨hb.2.2.1 B hB,?_⟩
  have hh := hb.2.2.2.2 B hB
  rw [entropy_power_rate] at hh
  exact hh

theorem EvenScaleLayers12.two_step_descendant_bounds {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex) {Q : AssignedPiece V}
    (hQ : Q∈advance L.splitter 0 (i+3) [originalPiece G]) :
    (Q.vertices.card:ℝ)≤(2:ℝ)^(b*logScale (originalLog V) L.stopIndex i)/2 ∧
    2*(edgeCount Q.graph:ℝ)≤entropyRemainder12 (q0*logScale (originalLog V) L.stopIndex i)*
      Q.vertices.card := by
  have hh := L.frontier_order_entropy (j:=i+2) (by omega) hQ
  have hs := (three_rate_two_step (theta0:=theta0) (theta1:=theta1) (theta2:=theta2)
    (by norm_num [theta2]) (by norm_num [theta2,theta1]) L.initial_log_pos.le hi).2
  have hs' : logScale (originalLog V) L.stopIndex (i+2)≤
      q0*logScale (originalLog V) L.stopIndex i := hs
  have hw := logScale_active L.initial_log_pos.le L.phase_lower hi
  refine ⟨hh.1.trans ((rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left hs' (by norm_num [rho]))).trans (descendant_half_batch hw)),?_⟩
  have hpos := (logScale_positive L.initial_log_pos.le L.phase_lower (by omega : i+2<L.stopIndex+3)).le
  have hm := entropyRemainder12_monotone hpos (hpos.trans hs') hs'
  exact hh.2.trans (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _))

/-- Every actual parent remainder at an active layer has a certified batch
decomposition after its next two stages. This includes the last active layer. -/
theorem EvenScaleLayers12.actual_descendant_batches {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex) {P : AssignedPiece V}
    (hP : P∈advance L.splitter 0 (i+1) [originalPiece G]) :
    Nonempty (GraphBatches
      (graphUnion ((advance L.splitter (i+1) 2 [P]).map AssignedPiece.graph))
      P.vertices ((2:ℝ)^(b*logScale (originalLog V) L.stopIndex i))
      (vertexMass (advance L.splitter (i+1) 2 [P]))) ∧
    2*(edgeCount (graphUnion ((advance L.splitter (i+1) 2 [P]).map AssignedPiece.graph)):ℝ)≤
      entropyRemainder12 (q0*logScale (originalLog V) L.stopIndex i)*
        vertexMass (advance L.splitter (i+1) 2 [P]) := by
  have hmem (Q : AssignedPiece V) (hQ : Q∈advance L.splitter (i+1) 2 [P]) :
      Q∈advance L.splitter 0 (i+3) [originalPiece G] := by
    have hh := advance_member_of_mem L.splitter (i+1) 2 hP hQ
    simpa only [show i+3=(i+1)+2 by omega,advance_add,Nat.zero_add] using hh
  have hb (Q : AssignedPiece V) (hQ : Q∈advance L.splitter (i+1) 2 [P]) :=
    L.two_step_descendant_bounds hi (hmem Q hQ)
  exact ⟨descendant_batches _ _ _ _ (rpow_pos_of_pos (by norm_num) _) (fun Q hQ => (hb Q hQ).1),
    assigned_union_degree _ (fun Q hQ => (hb Q hQ).2)⟩

end
end Cycle12.Even12
