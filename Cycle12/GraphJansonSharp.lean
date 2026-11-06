import Cycle12.JansonDependencyUpper
import Cycle12.Foundations.GraphJanson

namespace Cycle12
open Finset Cycle13 Real SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def graphJansonNeighborhood (G : SimpleGraph V) (e : G.edgeSet) : Finset G.edgeSet :=
  insert e (G.lineGraph.neighborFinset e)

def sampledFinsetEdgeCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (univ.filter (fun e : G.edgeSet => edgeVertexSet G e⊆S)).card

theorem sampled_finset_edge_count (G : SimpleGraph V) (S : Finset V) :
    (sampledFinsetEdgeCount G S:ℝ)=occurrenceCount (edgeVertexSet G) S := by
  unfold sampledFinsetEdgeCount occurrenceCount containsIndicator
  simp only [sum_boole]

theorem graph_janson_neighborhood_self (G : SimpleGraph V) (e : G.edgeSet) :
    e∈graphJansonNeighborhood G e := mem_insert_self _ _

theorem graph_janson_neighborhood_valid (G : SimpleGraph V) (e f : G.edgeSet)
    (hf : f∉graphJansonNeighborhood G e) : Disjoint (edgeVertexSet G e) (edgeVertexSet G f) := by
  have hne : e≠f := by
    intro he
    subst f
    exact hf (graph_janson_neighborhood_self G e)
  have hadj : ¬G.lineGraph.Adj e f := by
    intro h
    exact hf (mem_insert_of_mem ((G.lineGraph.mem_neighborFinset e f).mpr h))
  have hh := edgeDependencies_valid G e f hne (by
    intro h
    exact hadj (mem_filter.mp h).2)
  exact Finset.disjoint_coe.mp hh

theorem graph_janson_occurrence_mean (G : SimpleGraph V) (p : unitInterval) :
    occurrenceMean (edgeVertexSet G) p=(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2 := by
  unfold occurrenceMean
  simp only [edgeVertexSet_card,sum_const,card_univ,nsmul_eq_mul]

theorem graph_janson_lambda_bound (G : SimpleGraph V) (p : unitInterval) :
    occurrenceLambda (edgeVertexSet G) (graphJansonNeighborhood G) p ≤
      (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
        (∑ e : G.edgeSet, (G.lineGraph.degree e:ℝ))*(p:ℝ)^3 := by
  have hi (e : G.edgeSet) :
      (∑ f ∈ graphJansonNeighborhood G e, (p:ℝ)^(edgeVertexSet G e∪edgeVertexSet G f).card) ≤
        (p:ℝ)^2+(G.lineGraph.degree e:ℝ)*(p:ℝ)^3 := by
    rw [graphJansonNeighborhood,sum_insert (by simp),union_self,edgeVertexSet_card]
    apply add_le_add (le_refl _)
    calc
      _ ≤ ∑ _f ∈ G.lineGraph.neighborFinset e, (p:ℝ)^3 := by
        apply sum_le_sum
        intro f hf
        have hne : e≠f := ((G.lineGraph.mem_neighborFinset e f).mp hf).1
        exact pow_le_pow_of_le_one p.2.1 p.2.2 (edgeVertexSet_union_card G e f hne)
      _ = _ := by simp only [sum_const,nsmul_eq_mul,G.lineGraph.card_neighborFinset_eq_degree]
  have hh := sum_le_sum (s:=univ) (fun e _ => hi e)
  simpa only [occurrenceLambda,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,← sum_mul] using hh

/-- A sharp lower tail for actual retained edges. The available dependency
budget can subsequently be bounded by a maximum degree or a degree-square sum. -/
theorem graph_janson_full_lower_tail (G : SimpleGraph V) (p : unitInterval)
    (hm : 0 < (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)
    (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (subsetBernoulli (univ:Finset V) p).prob
        (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤ tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)) ≤
      exp (-fullJansonPhi tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)^2/
        ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
          (∑ e : G.edgeSet, (G.lineGraph.degree e:ℝ))*(p:ℝ)^3)) := by
  have hh := bernoulli_janson_full_lower_tail_upper univ (edgeVertexSet G) (fun _ => subset_univ _)
    (graphJansonNeighborhood G) (graph_janson_neighborhood_valid G) (graph_janson_neighborhood_self G)
    p (by rwa [graph_janson_occurrence_mean]) _ (graph_janson_lambda_bound G p) tau ht0 ht1
  simpa only [graph_janson_occurrence_mean,sampled_finset_edge_count] using hh

end
end Cycle12
