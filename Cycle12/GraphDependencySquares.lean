import Cycle12.GraphJansonSharp

namespace Cycle12
open Finset Cycle13 Real SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem graph_incidence_weighted_sum (G : SimpleGraph V) (f : V → ℝ) :
    (∑ e : G.edgeSet, ∑ v ∈ edgeVertexSet G e, f v)=∑ v, (G.degree v:ℝ)*f v := by
  have hi (e : G.edgeSet) : (∑ v ∈ edgeVertexSet G e, f v)=
      ∑ v, if v∈e.val then f v else 0 := by
    rw [← sum_filter]
    congr 1
    ext v
    simp [edgeVertexSet]
  simp_rw [hi]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul,incident_edges_card]

theorem graph_edge_endpoint_sum (G : SimpleGraph V) (f : V → ℝ) (e : G.edgeSet) :
    (∑ v ∈ edgeVertexSet G e, f v)=f e.val.out.1+f e.val.out.2 := by
  have hne : e.val.out.1≠e.val.out.2 := G.ne_of_adj (edge_out_adj G e)
  unfold edgeVertexSet
  conv_lhs => rw [← e.val.out_eq,Sym2.toFinset_mk_eq,sum_pair hne]

theorem graph_endpoint_degree_square_sum (G : SimpleGraph V) :
    (∑ e : G.edgeSet, ((G.degree e.val.out.1:ℝ)+G.degree e.val.out.2))=
      ∑ v, (G.degree v:ℝ)^2 := by
  have hh := graph_incidence_weighted_sum G (fun v => (G.degree v:ℝ))
  simpa only [graph_edge_endpoint_sum,pow_two] using hh

theorem graph_line_degree_square_bound (G : SimpleGraph V) :
    (∑ e : G.edgeSet, (G.lineGraph.degree e:ℝ)) ≤ ∑ v, (G.degree v:ℝ)^2 := by
  rw [← graph_endpoint_degree_square_sum]
  apply sum_le_sum
  intro e _
  have hh := lineGraph_degree_bound G e
  have hn : G.lineGraph.degree e ≤ G.degree e.val.out.1+G.degree e.val.out.2 := by omega
  exact_mod_cast hn

theorem graph_janson_square_lower_tail (G : SimpleGraph V) (p : unitInterval)
    (hm : 0 < (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)
    (Q : ℝ) (hQ : (∑ v, (G.degree v:ℝ)^2) ≤ Q)
    (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (subsetBernoulli (univ:Finset V) p).prob
        (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤ tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)) ≤
      exp (-fullJansonPhi tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)^2/
        ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+Q*(p:ℝ)^3)) := by
  apply (graph_janson_full_lower_tail G p hm tau ht0 ht1).trans
  apply full_janson_dependency_upper _ _ _ _ (full_janson_phi_nonneg tau ht0)
  · exact add_pos_of_pos_of_nonneg hm
      (mul_nonneg (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (pow_nonneg p.2.1 _))
  · exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
      ((graph_line_degree_square_bound G).trans hQ) (pow_nonneg p.2.1 _))

end
end Cycle12
