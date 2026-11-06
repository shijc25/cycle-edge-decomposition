import Cycle12.ActualFoldQuotients12
import Cycle12.SoftQuotientAssembly12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EvenScaleLayers12.fold_remainder_edges {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) :
    2*((graphUnion ((advance L.splitter 0 (i+3) [originalPiece G]).map AssignedPiece.graph)).edgeSet.ncard:ℝ) ≤
      entropyRemainder12 (q0*logScale (originalLog V) L.stopIndex i)*M*Fintype.card V := by
  have he := assigned_union_degree (advance L.splitter 0 (i+3) [originalPiece G])
    (fun Q hQ => (L.two_step_descendant_bounds hi hQ).2)
  have hw := logScale_active L.initial_log_pos.le L.phase_lower hi
  have hn := entropyRemainder12_nonneg (mul_nonneg (show 0 ≤ q0 by norm_num [q0,theta1,theta2])
    ((show 0 ≤ wA by norm_num [wA]).trans hw))
  have hm := mul_le_mul_of_nonneg_left (actual_layer_mass L (i:=i+3) (by omega)) hn
  have hh := he.trans hm
  simpa only [edgeCount,←SimpleGraph.card_edgeSet,Set.fintypeCard_eq_ncard,mul_assoc] using hh

namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

theorem batch_edge_count_exact (F : ActualFoldStage12 L i) :
    (∑ t : F.BatchIndex,(F.batchGraph t).edgeSet.ncard)=
      (graphUnion ((advance L.splitter 0 (i+3) [originalPiece G]).map AssignedPiece.graph)).edgeSet.ncard := by
  rw [←F.batch_graph_cover,ncard_iUnion_disjoint _ F.batch_graph_disjoint]

theorem local_batch_edge_count (F : ActualFoldStage12 L i) (t : F.BatchIndex) :
    (F.localBatchGraph t).edgeSet.ncard=(F.batchGraph t).edgeSet.ncard := by
  have he := induced_edges_of_supported (F.batchGraph t) (F.batchVertices t)
    (fun _ _ h => (F.batches t.1).supported t.2 h)
  have hh := Set.ncard_image_of_injective (F.localBatchGraph t).edgeSet
    (Sym2.map.injective (Subtype.val_injective (p:=fun v => v∈F.batchVertices t)))
  rw [show Sym2.map Subtype.val '' (F.localBatchGraph t).edgeSet=(F.batchGraph t).edgeSet from he] at hh
  exact hh.symm

theorem local_batch_edge_mass (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) :
    2*(∑ t : F.BatchIndex,((F.localBatchGraph t).edgeSet.ncard:ℝ)) ≤
      entropyRemainder12 (q0*logScale (originalLog V) L.stopIndex i)*M*Fintype.card V := by
  simp_rw [F.local_batch_edge_count]
  rw [←Nat.cast_sum,F.batch_edge_count_exact]
  exact L.fold_remainder_edges hi

/-- The total original quotient-edge budget pays the soft collision
charge, using the actual growing team capacity rather than its base cap. -/
theorem actual_soft_budget (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) :
    (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*
      (∑ t : F.BatchIndex,((F.localBatchGraph t).edgeSet.ncard:ℝ)) ≤
        lossV (logScale (originalLog V) L.stopIndex i)*Fintype.card V := by
  let w := logScale (originalLog V) L.stopIndex i
  let E : ℝ := ∑ t : F.BatchIndex,((F.localBatchGraph t).edgeSet.ncard:ℝ)
  have hw : wA ≤ w := logScale_active L.initial_log_pos.le L.phase_lower hi
  have hQ : (0:ℝ) < routingTeamSize w := Nat.cast_pos.mpr (growing_rounding_bounds hw).1
  have ha := routingAllowance_pos w
  have hc : 0 < c*teamGrowth w*routingAllowance w :=
    mul_pos (mul_pos (by norm_num [c]) (teamGrowth_pos w)) ha
  have hceil : c*teamGrowth w*routingAllowance w ≤ routingTeamSize w := Nat.le_ceil _
  have hratio := div_le_div_of_nonneg_left (show 0 ≤ gamma by norm_num [gamma]) hc hceil
  have hE0 : 0 ≤ E := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hfirst := mul_le_mul_of_nonneg_right hratio hE0
  have hm := F.local_batch_edge_mass hi
  have hE : E ≤ entropyRemainder12 (q0*w)*M*Fintype.card V/2 := by
    dsimp only [E,w]
    linarith only [hm]
  have hsecond := mul_le_mul_of_nonneg_left hE
    (div_nonneg (show 0 ≤ gamma by norm_num [gamma]) hc.le)
  have he : gamma/(c*teamGrowth w*routingAllowance w)*
      (entropyRemainder12 (q0*w)*M*Fintype.card V/2)=lossV w*Fintype.card V := by
    rw [lossV_identity,←entropy_deficit_ratio]
    unfold routingAllowance
    ring
  exact hfirst.trans (hsecond.trans_eq he)

end ActualFoldStage12
end
end Cycle12.Even12
