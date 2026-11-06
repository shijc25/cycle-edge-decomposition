import Cycle12.FixedSampleGroundJanson
import Cycle12.JansonEdgeMassAlgebra

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_graph_ground_line_janson (G : SimpleGraph V) (D : Finset V)
    (hD : ∀ e : G.edgeSet, edgeVertexSet G e⊆D) (p : unitInterval)
    {k : ℕ} (hk : k ≤ D.card) (hmean : (D.card:ℝ)*(p:ℝ)=(k:ℝ))
    (hp : (p:ℝ) ≤ 1/2) (hm : 0<(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)
    (Q : ℝ) (hQ : (∑ e : G.edgeSet, (G.lineGraph.degree e:ℝ)) ≤ Q)
    (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (fixedSizeLaw D k).prob
        (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤ tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2))  ≤ 
      2*Real.exp (-fullJansonPhi tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)^2/
        ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+Q*(p:ℝ)^3)) := by
  have hB : occurrenceLambda (edgeVertexSet G) (graphJansonNeighborhood G) p  ≤ 
      (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+Q*(p:ℝ)^3 := by
    exact (graph_janson_lambda_bound G p).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hQ (pow_nonneg p.2.1 _)))
  have hh := fixed_occurrence_full_janson D (edgeVertexSet G) hD (graphJansonNeighborhood G)
    (graph_janson_neighborhood_valid G) (graph_janson_neighborhood_self G) p hk hmean hp
    (by rwa [graph_janson_occurrence_mean]) _ hB tau ht0 ht1
  simpa only [graph_janson_occurrence_mean,sampled_finset_edge_count] using hh

/-- A lower bound on the retained number of edges is used only after
proving monotonicity of the complete exponent, including its denominator. -/
theorem fixed_graph_quadratic_janson (G : SimpleGraph V) (D : Finset V)
    (hD : ∀ e : G.edgeSet, edgeVertexSet G e⊆D) (p : unitInterval)
    {k : ℕ} (hk : k ≤ D.card) (hmean : (D.card:ℝ)*(p:ℝ)=(k:ℝ))
    (hp : (p:ℝ) ≤ 1/2) (hp0 : 0<(p:ℝ))
    {M a b : ℝ} (hM : 0<M) (hMm : M ≤ (Fintype.card G.edgeSet:ℝ))
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hQ : (∑ e : G.edgeSet, (G.lineGraph.degree e:ℝ))  ≤ 
      a*(Fintype.card G.edgeSet:ℝ)+b*(Fintype.card G.edgeSet:ℝ)^2)
    (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (fixedSizeLaw D k).prob (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤ tau*(M*(p:ℝ)^2))  ≤ 
      2*Real.exp (-fullJansonPhi tau*M*(p:ℝ)^2/(1+(a+b*M)*(p:ℝ))) := by
  have hm : 0<(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2 :=
    mul_pos (hM.trans_le hMm) (sq_pos_of_pos hp0)
  have he : (fixedSizeLaw D k).prob
      (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤ tau*(M*(p:ℝ)^2))  ≤ 
      (fixedSizeLaw D k).prob
      (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤ tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)) := by
    apply FiniteLaw.prob_mono
    intro S hS
    exact hS.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hMm (sq_nonneg _)) ht0)
  apply (he.trans (fixed_graph_ground_line_janson G D hD p hk hmean hp hm _ hQ tau ht0 ht1)).trans
  have hbnd := janson_edge_exp_mass_mono (full_janson_phi_nonneg tau ht0) hM hMm hp0 ha hb
  have hn := janson_edge_rate_cancel (-fullJansonPhi tau) M p a b hM.ne' hp0.ne'
  rw [hn] at hbnd
  exact mul_le_mul_of_nonneg_left hbnd (by norm_num)

end
end Cycle12
