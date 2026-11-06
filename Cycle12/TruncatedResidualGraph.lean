import Cycle12.RetainedVertexGraph
import Cycle12.BipartiteRectangle
import Cycle12.LineGraphDegreeExact
import Cycle12.ProfileTruncation

namespace Cycle12
open Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem truncated_subgraph_bipartite (G H : SimpleGraph V) (S : Finset V) (k : ℕ)
    (hH : H≤truncatedCut G S k) : H.IsBipartiteWith (S:Set V) (Sᶜ:Set V) := by
  have hb := truncatedCut_bipartite G S k
  refine ⟨disjoint_compl_right,?_⟩
  intro v w hvw
  simpa only [Finset.coe_compl] using hb.mem_of_adj (hH hvw)

theorem truncated_subgraph_rectangle (G H : SimpleGraph V) (S : Finset V) (k : ℕ)
    (hH : H≤truncatedCut G S k) (hk : 0<k) (hS : S.card≤k) :
    (∑ v, (H.degree v:ℝ)^2) ≤
      (k:ℝ)*(Fintype.card H.edgeSet:ℝ)+(Fintype.card H.edgeSet:ℝ)^2/k := by
  apply bipartite_rectangle_degree_square_bound H S
    (truncated_subgraph_bipartite G H S k hH) k
    (by exact_mod_cast hk) (by exact_mod_cast hS)
  intro v hv
  have hh : H.degree v≤k := (SimpleGraph.degree_le_of_le hH).trans
    (by rw [truncatedCut_degree_left G S k hv]; exact min_le_left _ _)
  exact_mod_cast hh

/-- The line-graph degree retains the subtraction by two. This pays for
the ceiling in the capped degree when the endpoint bound is used. -/
theorem truncated_subgraph_line_bound (G H : SimpleGraph V) (S : Finset V) (k : ℕ)
    (hH : H≤truncatedCut G S k) :
    (∑ e : H.edgeSet, (H.lineGraph.degree e:ℝ)) ≤
      (Fintype.card H.edgeSet:ℝ)*((k:ℝ)+S.card-2) := by
  have hp (e : H.edgeSet) : (H.lineGraph.degree e:ℝ)≤(k:ℝ)+S.card-2 := by
    have hd₁ := SimpleGraph.degree_le_of_le (v:=e.val.out.1) hH
    have hd₂ := SimpleGraph.degree_le_of_le (v:=e.val.out.2) hH
    have hb := truncatedCut_endpoint_sum G S k (hH (edge_out_adj H e))
    have he := line_graph_degree_exact H e
    have hn : H.lineGraph.degree e+2≤k+S.card := by omega
    have hr : (H.lineGraph.degree e:ℝ)+2≤(k:ℝ)+S.card := by exact_mod_cast hn
    linarith
  calc
    _ ≤ ∑ _e : H.edgeSet, ((k:ℝ)+S.card-2) := sum_le_sum (fun e _ => hp e)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

def truncatedResidualGraph (G : SimpleGraph V) (S T : Finset V) (k : ℕ) : SimpleGraph V :=
  retainedVertexGraph (truncatedCut G S k) (univ\T)

theorem truncated_residual_le (G : SimpleGraph V) (S T : Finset V) (k : ℕ) :
    truncatedResidualGraph G S T k≤truncatedCut G S k :=
  retained_vertex_graph_le _ _

theorem truncated_residual_retention (G : SimpleGraph V) (S T : Finset V) (k : ℕ)
    (hk : S.card≤k) :
    (Fintype.card (truncatedCut G S k).edgeSet:ℝ)-(k:ℝ)*T.card ≤
      (Fintype.card (truncatedResidualGraph G S T k).edgeSet:ℝ) :=
  retained_vertex_graph_deletion_bound _ T (fun v _ => truncatedCut_degree_bound G S k hk v)

theorem truncated_residual_profile (G : SimpleGraph V) (S T : Finset V) (k : ℕ)
    (alpha : ℝ → ℝ) {h N lambda : ℝ} (hh : 0<h) (hN : 0<N) (hS : S.Nonempty)
    (hk : S.card≤k) (hcap : lambda*S.card≤(k:ℝ))
    (hprofile : ∀ X⊆S, alpha ((X.card:ℝ)/N)*h*X.card≤(cutSize G X:ℝ)) :
    ∃ t : ℝ, 0≤t ∧ t≤1 ∧
      (S.card/h)*(1-t)*(lambda-t)+t*alpha (t*(S.card/h)/(N/h))-
        (k:ℝ)*T.card/(h*S.card) ≤
          (Fintype.card (truncatedResidualGraph G S T k).edgeSet:ℝ)/(h*S.card) := by
  obtain ⟨t,ht0,ht1,ht⟩ := truncated_cut_full_profile_scaled G S k alpha hh hN hS hcap hprofile
  have hd := truncated_residual_retention G S T k hk
  have he : (truncatedCut G S k).edgeSet.ncard=Fintype.card (truncatedCut G S k).edgeSet := by
    simp only [Set.ncard_eq_toFinset_card',Set.toFinset_card]
  rw [he] at ht
  refine ⟨t,ht0,ht1,?_⟩
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hb := div_le_div_of_nonneg_right hd (mul_pos hh hs).le
  rw [sub_div] at hb
  linarith

theorem sampled_truncated_residual_cut_le (G : SimpleGraph V) (S T U R : Finset V)
    (k : ℕ) (hRU : R⊆U) :
    sampledFinsetEdgeCount (truncatedResidualGraph G S T k) R ≤
      (G.interedges (U∩S) (U\S)).card := by
  have hcut : truncatedResidualGraph G S T k≤cutGraph G S := by
    intro v w hvw
    have hh := truncated_residual_le G S T k hvw
    refine ⟨truncatedCut_le G S k hh,?_⟩
    simpa only [Finset.coe_compl] using (truncatedCut_bipartite G S k).mem_of_adj hh
  have hmono : sampledFinsetEdgeCount (truncatedResidualGraph G S T k) R ≤
      sampledFinsetEdgeCount (truncatedResidualGraph G S T k) U := by
    unfold sampledFinsetEdgeCount
    apply card_le_card
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2.trans hRU⟩
  apply hmono.trans
  rw [sampled_finset_edge_count_eq_sampled,← sampled_cut_edge_count G S U]
  exact sampledEdgeCount_mono hcut _

end
end Cycle12
