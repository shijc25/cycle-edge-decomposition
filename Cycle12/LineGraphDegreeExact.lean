import Cycle12.GraphDependencySquares

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem line_graph_degree_exact (G : SimpleGraph V) (e : G.edgeSet) :
    G.lineGraph.degree e+2=G.degree e.val.out.1+G.degree e.val.out.2 := by
  let A : Finset G.edgeSet := univ.filter (fun f => e.val.out.1∈f.val)
  let B : Finset G.edgeSet := univ.filter (fun f => e.val.out.2∈f.val)
  have hA : e∈A := mem_filter.mpr ⟨mem_univ _,Sym2.out_fst_mem _⟩
  have hB : e∈B := mem_filter.mpr ⟨mem_univ _,Sym2.out_snd_mem _⟩
  have hdis : Disjoint (A.erase e) (B.erase e) := by
    apply Finset.disjoint_left.mpr
    intro f hfA hfB
    have hf1 : e.val.out.1∈f.val := (mem_filter.mp (mem_erase.mp hfA).2).2
    have hf2 : e.val.out.2∈f.val := (mem_filter.mp (mem_erase.mp hfB).2).2
    have he : f=e := Subtype.ext (Sym2.eq_of_ne_mem (G.ne_of_adj (edge_out_adj G e))
      hf1 hf2 (Sym2.out_fst_mem _) (Sym2.out_snd_mem _))
    exact (mem_erase.mp hfA).1 he
  have hn : G.lineGraph.neighborFinset e=A.erase e∪B.erase e := by
    ext f
    rw [G.lineGraph.mem_neighborFinset,SimpleGraph.lineGraph_adj_iff_exists]
    constructor
    · rintro ⟨hne,v,hve,hvf⟩
      rw [← e.val.out_eq,Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · exact mem_union_left _ (mem_erase.mpr ⟨hne.symm,mem_filter.mpr ⟨mem_univ _,hvf⟩⟩)
      · exact mem_union_right _ (mem_erase.mpr ⟨hne.symm,mem_filter.mpr ⟨mem_univ _,hvf⟩⟩)
    · intro hf
      rcases mem_union.mp hf with hf | hf
      · exact ⟨(mem_erase.mp hf).1.symm,e.val.out.1,Sym2.out_fst_mem _,
          (mem_filter.mp (mem_erase.mp hf).2).2⟩
      · exact ⟨(mem_erase.mp hf).1.symm,e.val.out.2,Sym2.out_snd_mem _,
          (mem_filter.mp (mem_erase.mp hf).2).2⟩
  have hc := congrArg Finset.card hn
  rw [G.lineGraph.card_neighborFinset_eq_degree,card_union_of_disjoint hdis] at hc
  have ha := card_erase_add_one hA
  have hb := card_erase_add_one hB
  have hca : A.card=G.degree e.val.out.1 := incident_edges_card G _
  have hcb : B.card=G.degree e.val.out.2 := incident_edges_card G _
  omega

theorem line_graph_total_degree_exact (G : SimpleGraph V) :
    (∑ e : G.edgeSet, (G.lineGraph.degree e:ℝ))=
      (∑ v, (G.degree v:ℝ)^2)-2*(Fintype.card G.edgeSet:ℝ) := by
  have hi (e : G.edgeSet) : (G.lineGraph.degree e:ℝ)+2=
      (G.degree e.val.out.1:ℝ)+G.degree e.val.out.2 := by
    exact_mod_cast line_graph_degree_exact G e
  have hh := sum_congr (s₁:=univ) rfl (fun e _ => hi e)
  rw [sum_add_distrib,graph_endpoint_degree_square_sum] at hh
  simp only [sum_const,card_univ,nsmul_eq_mul] at hh
  linarith

end
end Cycle12
