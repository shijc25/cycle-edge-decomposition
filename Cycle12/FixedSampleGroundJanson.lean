import Cycle12.FixedSizeFactorTwo

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem fixed_occurrence_full_janson (D : Finset V) (E : I → Finset V)
    (hE : ∀ i, E i⊆D) (K : I → Finset I)
    (hK : ∀ i j, j∉K i → Disjoint (E i) (E j)) (hself : ∀ i, i∈K i)
    (p : unitInterval) {k : ℕ} (hk : k≤D.card)
    (hmean : (D.card:ℝ)*(p:ℝ)=(k:ℝ)) (hp : (p:ℝ)≤1/2)
    (hm : 0<occurrenceMean E p) (B : ℝ) (hB : occurrenceLambda E K p≤B)
    (tau : ℝ) (ht0 : 0≤tau) (ht1 : tau≤1) :
    (fixedSizeLaw D k).prob (fun S => occurrenceCount E S≤tau*occurrenceMean E p) ≤
      2*Real.exp (-fullJansonPhi tau*(occurrenceMean E p)^2/B) := by
  apply (fixed_size_decreasing_factor_two D p hk hmean hp _ ?_).trans
  · exact mul_le_mul_of_nonneg_left
      (bernoulli_janson_full_lower_tail_upper D E hE K hK hself p hm B hB tau ht0 ht1)
      (by norm_num)
  · intro S T hST hT
    exact (sum_le_sum (fun i _ => contains_indicator_monotone (E i) hST)).trans hT

/-- Sampling a residual vertex domain: this allows deleting the marked
vertices before applying the fixed-size sharp tail to the remaining edges. -/
theorem fixed_graph_ground_janson (G : SimpleGraph V) (D : Finset V)
    (hD : ∀ e : G.edgeSet, edgeVertexSet G e⊆D) (p : unitInterval)
    {k : ℕ} (hk : k≤D.card) (hmean : (D.card:ℝ)*(p:ℝ)=(k:ℝ))
    (hp : (p:ℝ)≤1/2) (hm : 0<(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)
    (Q : ℝ) (hQ : (∑ v, (G.degree v:ℝ)^2)≤Q)
    (tau : ℝ) (ht0 : 0≤tau) (ht1 : tau≤1) :
    (fixedSizeLaw D k).prob
        (fun S => (sampledFinsetEdgeCount G S:ℝ)≤tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)) ≤
      2*Real.exp (-fullJansonPhi tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)^2/
        ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+Q*(p:ℝ)^3)) := by
  have hB : occurrenceLambda (edgeVertexSet G) (graphJansonNeighborhood G) p ≤
      (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+Q*(p:ℝ)^3 := by
    apply (graph_janson_lambda_bound G p).trans
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
      ((graph_line_degree_square_bound G).trans hQ) (pow_nonneg p.2.1 _))
  have hh := fixed_occurrence_full_janson D (edgeVertexSet G) hD (graphJansonNeighborhood G)
    (graph_janson_neighborhood_valid G) (graph_janson_neighborhood_self G) p hk hmean hp
    (by rwa [graph_janson_occurrence_mean]) _ hB tau ht0 ht1
  simpa only [graph_janson_occurrence_mean,sampled_finset_edge_count] using hh

end
end Cycle12
