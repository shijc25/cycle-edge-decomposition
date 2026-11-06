import Cycle12.LineGraphDegreeExact

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem edge_vertex_union_card_adjacent (G : SimpleGraph V) (e f : G.edgeSet)
    (hadj : G.lineGraph.Adj e f) : (edgeVertexSet G e∪edgeVertexSet G f).card=3 := by
  have hl := edgeVertexSet_union_card G e f hadj.1
  obtain ⟨_,v,hve,hvf⟩ := lineGraph_adj_iff_exists.mp hadj
  have hi : 0<(edgeVertexSet G e∩edgeVertexSet G f).card :=
    card_pos.mpr ⟨v,mem_inter.mpr ⟨by simpa [edgeVertexSet] using hve,
      by simpa [edgeVertexSet] using hvf⟩⟩
  have hh := card_union_add_card_inter (edgeVertexSet G e) (edgeVertexSet G f)
  rw [edgeVertexSet_card,edgeVertexSet_card] at hh
  omega

theorem edge_vertex_union_card_disjoint (G : SimpleGraph V) (e f : G.edgeSet)
    (hne : e≠f) (hadj : ¬G.lineGraph.Adj e f) : (edgeVertexSet G e∪edgeVertexSet G f).card=4 := by
  have hd := graph_janson_neighborhood_valid G e f (by
    intro hf
    rcases mem_insert.mp hf with he | hf
    · exact hne he.symm
    · exact hadj ((G.lineGraph.mem_neighborFinset e f).mp hf))
  rw [card_union_of_disjoint hd,edgeVertexSet_card,edgeVertexSet_card]

/-- Counting all ordered edge pairs by equality, a common endpoint, or
four distinct endpoints. -/
theorem ordered_edge_pair_function_sum (G : SimpleGraph V) (a b c : ℝ) :
    (∑ e : G.edgeSet, ∑ f : G.edgeSet, if e=f then a else if G.lineGraph.Adj e f then b else c)=
      (Fintype.card G.edgeSet:ℝ)*a+
      ((∑ v, (G.degree v:ℝ)^2)-2*(Fintype.card G.edgeSet:ℝ))*b+
      ((Fintype.card G.edgeSet:ℝ)^2+(Fintype.card G.edgeSet:ℝ)-(∑ v, (G.degree v:ℝ)^2))*c := by
  have he (e f : G.edgeSet) : (if e=f then a else if G.lineGraph.Adj e f then b else c)=
      c+(if e=f then a-c else 0)+(if G.lineGraph.Adj e f then b-c else 0) := by
    by_cases hef : e=f
    · subst f
      simp
    · simp only [if_neg hef]
      split_ifs <;> ring
  have hn (e : G.edgeSet) : (∑ f : G.edgeSet, if G.lineGraph.Adj e f then b-c else 0)=
      (G.lineGraph.degree e:ℝ)*(b-c) := by
    rw [← sum_filter]
    have hfilter : univ.filter (G.lineGraph.Adj e)=G.lineGraph.neighborFinset e := by ext f; simp
    rw [hfilter]
    simp only [sum_const,nsmul_eq_mul,G.lineGraph.card_neighborFinset_eq_degree]
  simp_rw [he,sum_add_distrib]
  simp only [sum_ite_eq,mem_univ,ite_true,hn,sum_const,card_univ,nsmul_eq_mul,← sum_mul,
    line_graph_total_degree_exact]
  ring

end
end Cycle12
