import Cycle12.ActualRouteCover12
import Cycle12.ActualFoldSoftBudget12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem quotientRouteEdges_subset (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    F.quotientRouteEdges P Q D hi t⊆G.edgeSet := by
  apply Set.iUnion_subset
  intro j
  exact Set.iUnion_subset (fun z => (F.actualQuotientRoute P Q D hi t j z).edges_subset_edgeSet)

def actualQuotientGraph (hi : i≤L.stopIndex) (t : F.BatchIndex) : SimpleGraph V :=
  fromEdgeSet ((F.ambientBatchRetained P t).edgeSet∪F.quotientRouteEdges P Q D hi t)

theorem actualQuotientGraph_edges (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    (F.actualQuotientGraph P Q D hi t).edgeSet=
      (F.ambientBatchRetained P t).edgeSet∪F.quotientRouteEdges P Q D hi t := by
  rw [actualQuotientGraph,edgeSet_fromEdgeSet]
  apply Set.Subset.antisymm Set.sdiff_subset
  intro e he
  refine ⟨he,G.edgeSet_subset_compl_diagSet ?_⟩
  rcases he with he|he
  · exact edgeSet_mono ((F.ambient_retained_le P t).trans (F.batch_graph_le_original t)) he
  · exact F.quotientRouteEdges_subset P Q D hi t he

theorem actualQuotientGraph_le (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    F.actualQuotientGraph P Q D hi t≤G := by
  apply edgeSet_subset_edgeSet.mp
  rw [F.actualQuotientGraph_edges P Q D hi t]
  exact Set.union_subset (edgeSet_mono ((F.ambient_retained_le P t).trans (F.batch_graph_le_original t)))
    (F.quotientRouteEdges_subset P Q D hi t)

theorem quotient_cycle_routes_disjoint (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    Pairwise (fun j k : Fin (Q t).count =>
      Disjoint (⋃ z,(F.actualQuotientRoute P Q D hi t j z).edgeSet)
        (⋃ z,(F.actualQuotientRoute P Q D hi t k z).edgeSet)) := by
  intro j k hjk
  apply Set.disjoint_iUnion_left.mpr
  intro z
  apply Set.disjoint_iUnion_right.mpr
  intro y
  apply F.boxRoute_edges_disjoint P Q D hi t.1
  intro he
  have hh := eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Sum.inr.inj he))).2
  exact hjk (congrArg Sigma.fst hh)

theorem quotient_retained_routes_disjoint (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    Disjoint (F.ambientBatchRetained P t).edgeSet (F.quotientRouteEdges P Q D hi t) := by
  apply Set.disjoint_iUnion_right.mpr
  intro j
  apply Set.disjoint_iUnion_right.mpr
  intro z
  exact (F.boxRoute_descendant_disjoint P Q D hi t.1 _ t.1).symm.mono
    (edgeSet_mono ((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2))) subset_rfl

theorem actual_quotient_batch_closure (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    ∃ T : CyclePacking G,
      T.used=((F.ambientBatchRetained P t).edgeSet∩
        Sym2.map (contractVertex (F.ambientBatchActive t)) ⁻¹' (Q t).used)∪F.quotientRouteEdges P Q D hi t ∧
      (T.count:ℝ)≤(Q t).count+
        (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*(Q t).used.ncard := by
  choose T ht hc using fun j => F.actual_quotient_cycle_closure P Q D hi t j
  obtain ⟨R,hr,hcount⟩ := quotient_cycle_family_assembly G (F.ambientBatchRetained P t)
    (contractVertex (F.ambientBatchActive t)) (Q t) T
    (fun j => ⋃ z,(F.actualQuotientRoute P Q D hi t j z).edgeSet)
    (fun j => by rw [ht j,(D t).outline_edges (F.ambient_quotient_unique P t) j])
    (F.quotient_cycle_routes_disjoint P Q D hi t)
    (fun j => (F.quotient_retained_routes_disjoint P Q D hi t).mono_right
      (fun _ he => Set.mem_iUnion.mpr ⟨j,he⟩))
    (fun j => (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*((D t).walk j).length) hc
  refine ⟨R,hr,?_⟩
  have he := ((D t).total_length (F.ambient_quotient_proper P t) (F.ambient_quotient_unique P t)).1
  have he' : (∑ j : Fin (Q t).count,(((D t).walk j).length:ℝ))=((Q t).used.ncard:ℝ) := by
    exact_mod_cast he
  simpa only [←mul_sum,he'] using hcount

/-- The singleton representatives left by the quotient packing are kept
exactly once; adding the joint routes changes only the cycle count. -/
theorem actual_quotient_batch_weight (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    ∃ T : CyclePacking (F.actualQuotientGraph P Q D hi t),
      T.weight≤(Q t).weight+
        (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*(F.localBatchGraph t).edgeSet.ncard := by
  obtain ⟨R,hr,hcount⟩ := F.actual_quotient_batch_closure P Q D hi t
  have hs : R.used⊆(F.actualQuotientGraph P Q D hi t).edgeSet := by
    rw [hr,F.actualQuotientGraph_edges P Q D hi t]
    exact Set.union_subset_union Set.inter_subset_left subset_rfl
  let T := restrictPacking R (F.actualQuotientGraph P Q D hi t) hs
  have ht := lifted_quotient_weight (F.actualQuotientGraph P Q D hi t)
    (F.ambientBatchRetained P t) (contractVertex (F.ambientBatchActive t))
    (F.ambient_quotient_proper P t) (F.ambient_quotient_unique P t) (Q t) T
    (F.quotientRouteEdges P Q D hi t) (F.actualQuotientGraph_edges P Q D hi t)
    (F.quotient_retained_routes_disjoint P Q D hi t) hr hcount
  have hmass : (Q t).used.ncard≤(F.localBatchGraph t).edgeSet.ncard := by
    rw [F.local_batch_edge_count t]
    exact (((D t).total_length (F.ambient_quotient_proper P t) (F.ambient_quotient_unique P t)).2).trans
      (Set.ncard_le_ncard (edgeSet_mono (F.ambient_retained_le P t)))
  refine ⟨T,ht.trans ?_⟩
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast hmass
  · exact div_nonneg (by norm_num [gamma]) (Nat.cast_nonneg _)

theorem actual_quotient_family_weight (hi : i≤L.stopIndex) :
    ∃ T : ∀ t : F.BatchIndex,CyclePacking (F.actualQuotientGraph P Q D hi t),
      (∑ t,(T t).weight)≤(∑ t,(Q t).weight)+
        lossV (logScale (originalLog V) L.stopIndex i)*Fintype.card V := by
  choose T ht using fun t => F.actual_quotient_batch_weight P Q D hi t
  refine ⟨T,?_⟩
  have hs := sum_le_sum (fun t (_ : t∈(univ:Finset F.BatchIndex)) => ht t)
  rw [sum_add_distrib,←mul_sum] at hs
  exact hs.trans (add_le_add_right (F.actual_soft_budget hi) _)

end ActualFoldStage12
end
end Cycle12.Even12
