import Cycle12.PreparedIncidenceBudget12
import Cycle12.ActualFoldQuotients12
import Cycle12.GlobalFoldLedger12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

theorem local_batch_good_degree (F : ActualFoldStage12 L i) (t : F.BatchIndex)
    (r : (F.active t.1).Index t.2) (v : F.batchVertices t) (hv : v∈F.batchActive t r) :
    ((F.localBatchGraph t).degree v:ℝ) ≤ routingAllowance (logScale (originalLog V) L.stopIndex i) := by
  have he : (F.localBatchGraph t).degree v=(F.batchGraph t).degree v.val := by
    have hh := (F.batchGraph t).degree_induce_of_neighborSet_subset
      (s:=(F.batchVertices t:Set V)) (v:=v)
      (fun _ hy => ((F.batches t.1).supported t.2 hy).2)
    convert hh using 1 <;> congr!
  rw [he]
  have hd : ((F.batchGraph t).degree v.val:ℝ) ≤ (L.foldDescendantGraph i t.1).degree v.val := by
    exact_mod_cast (F.batchGraph t).degree_le_of_le ((F.batches t.1).graph_le t.2) (v:=v.val)
  exact hd.trans ((F.active t.1).degree_le t.2 r v.val ((mem_verticesWithin _ _ v).mp hv))

def preparedPairCount (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) : ℝ :=
  ∑ t : F.BatchIndex,(Fintype.card (P t).pairs.Index:ℝ)

def preparedMatchingMass (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) : ℝ :=
  ∑ t : F.BatchIndex,((P t).matchingEdges.ncard:ℝ)

/-- The combined path and matching charge is bounded using the actual
original incidences, once for each actual batch active-set occurrence. -/
theorem prepared_incidence_budget (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) :
    2*F.preparedPairCount P+F.preparedMatchingMass P ≤
      routingAllowance (logScale (originalLog V) L.stopIndex i)*F.activeMass := by
  have ht (t : F.BatchIndex) : 2*(Fintype.card (P t).pairs.Index:ℝ)+(P t).matchingEdges.ncard ≤
      routingAllowance (logScale (originalLog V) L.stopIndex i)*
        ∑ r,(((F.active t.1).vertices t.2 r).card:ℝ) := by
    have hh := (P t).original_pair_matching_budget_real (F.batchActive_disjoint t)
      (F.local_batch_good_degree t)
    simpa only [F.batchActive_card] using hh
  have hh := sum_le_sum (fun t (_ : t∈(univ:Finset F.BatchIndex)) => ht t)
  simp only [sum_add_distrib,←mul_sum] at hh
  have he : (∑ t : F.BatchIndex,∑ j,(((F.active t.1).vertices t.2 j).card:ℝ))=F.activeMass := by
    rw [Fintype.sum_sigma]
    rfl
  rwa [he] at hh

/-- The growing team capacity pays all pair-group and matching-group
size terms from the same original-incidence budget. Color and class
ceiling costs are accounted for separately by their actual counts. -/
theorem actual_group_size_budget (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex)
    (P : ∀ t,F.BatchPreparation t) :
    F.preparedPairCount P/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ)+
      F.preparedMatchingMass P/(2*routingTeamSize (logScale (originalLog V) L.stopIndex i)) ≤
      groupFee (logScale (originalLog V) L.stopIndex i)*F.activeMass := by
  let w := logScale (originalLog V) L.stopIndex i
  have hw : wA ≤ w := logScale_active L.initial_log_pos.le L.phase_lower hi
  have hQ : (0:ℝ) < routingTeamSize w := Nat.cast_pos.mpr (growing_rounding_bounds hw).1
  have hcg : 0 < c*teamGrowth w := mul_pos (by norm_num [c]) (teamGrowth_pos w)
  have hceil : c*teamGrowth w*routingAllowance w ≤ routingTeamSize w := Nat.le_ceil _
  have hr : routingAllowance w/(2*routingTeamSize w) ≤ groupFee w := by
    rw [groupFee_identity]
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 2*routingTeamSize w)
      (by nlinarith only [hcg] : (0:ℝ) < 2*c*teamGrowth w)).mpr
    nlinarith only [hceil]
  calc
    _ = (2*F.preparedPairCount P+F.preparedMatchingMass P)/(2*routingTeamSize w) := by ring
    _ ≤ (routingAllowance w*F.activeMass)/(2*routingTeamSize w) :=
      div_le_div_of_nonneg_right (F.prepared_incidence_budget P) (by positivity)
    _ = (routingAllowance w/(2*routingTeamSize w))*F.activeMass := by ring
    _ ≤ groupFee w*F.activeMass := mul_le_mul_of_nonneg_right hr F.activeMass_nonneg

end ActualFoldStage12
end
end Cycle12.Even12
