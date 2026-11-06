import Cycle12.Foundations.TruncatedCutRetention
import Cycle12.Foundations.VertexDeletionEdges
import Cycle12.Foundations.FiniteGraphJanson

namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem truncatedCut_after_marks (G : SimpleGraph V) (S T : Finset V) (k : ℕ)
    (a L : ℝ) (hk : S.card≤k) (hcap : L*S.card≤(k:ℝ))
    (hprofile : ∀ X⊆S, a*X.card≤(cutSize G X:ℝ)) :
    a*S.card-(max (a-(L-1)*S.card) 0)^2/4-(k:ℝ)*T.card ≤
      (Fintype.card ((truncatedCut G S k).induce (↑(univ\T):Set V)).edgeSet:ℝ) := by
  rw [edgeSet_card_eq_inducedEdgeCount]
  have hr := truncatedCut_retained_scaled_cap G S k a L hcap hprofile
  have hd := edge_count_delete_vertices_bounded (truncatedCut G S k) T
    (fun v _ => truncatedCut_degree_bound G S k hk v)
  linarith

theorem truncatedCut_unmarked_endpoint_sum (G : SimpleGraph V) (S T : Finset V) (k : ℕ)
    (hks : 2≤k+S.card) {v w : (↑(univ\T):Set V)}
    (h : ((truncatedCut G S k).induce (↑(univ\T):Set V)).Adj v w) :
    ((truncatedCut G S k).induce (↑(univ\T):Set V)).degree v+
      ((truncatedCut G S k).induce (↑(univ\T):Set V)).degree w≤(k+S.card-2)+2 := by
  have hv := degree_induced_le (truncatedCut G S k) (univ\T) v
  have hw := degree_induced_le (truncatedCut G S k) (univ\T) w
  have hb := truncatedCut_endpoint_sum G S k (v:=v.val) (w:=w.val) h
  simp only [← ncard_neighborSet] at hv hw hb ⊢
  omega

theorem finite_graph_janson_fraction (G : SimpleGraph V) (p : unitInterval) {D : ℕ}
    (hD : ∀ v w, G.Adj v w → G.degree v+G.degree w≤D+2)
    {τ : ℝ} (hτ0 : 0≤τ) (hτ1 : τ≤1) :
    (bernoulliSubset (V:=V) p).prob (fun S => (sampledEdgeCount G (S:Set V):ℝ)≤
      τ*(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2) ≤
    exp (-(1-τ)^2*(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2/(2*(1+(D:ℝ)*(p:ℝ)))) := by
  let m : ℝ := Fintype.card G.edgeSet
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hp := p.2.1
  by_cases hz : m*(p:ℝ)^2=0
  · have he : -(1-τ)^2*m*(p:ℝ)^2=0 := by nlinarith
    change _ ≤ exp (-(1-τ)^2*m*(p:ℝ)^2/(2*(1+(D:ℝ)*(p:ℝ))))
    rw [he,zero_div,exp_zero]
    exact FiniteLaw.prob_le_one _ _
  have hmp : 0 < m*(p:ℝ)^2 := lt_of_le_of_ne (mul_nonneg hm (sq_nonneg _)) (Ne.symm hz)
  have hm0 : m≠0 := by intro h; simp [h] at hz
  have hp0 : (p:ℝ)≠0 := by intro h; simp [h] at hz
  have ht0 : 0≤(1-τ)*m*(p:ℝ)^2 := by nlinarith
  have ht : (1-τ)*m*(p:ℝ)^2 ≤ m*(p:ℝ)^2 := by nlinarith
  have hh := finite_graph_janson G p hD ht0 ht
  have hevent : (fun S : Finset V => (sampledEdgeCount G (S:Set V):ℝ)≤τ*m*(p:ℝ)^2)=
      (fun S : Finset V => (sampledEdgeCount G (S:Set V):ℝ) ≤ m*(p:ℝ)^2-(1-τ)*m*(p:ℝ)^2) := by
    funext S; congr 1; ring
  change (bernoulliSubset (V:=V) p).prob
    (fun S : Finset V => (sampledEdgeCount G (S:Set V):ℝ)≤τ*m*(p:ℝ)^2) ≤ _
  rw [hevent]
  apply hh.trans_eq
  congr 1
  change -((1-τ)*m*(p:ℝ)^2)^2/(2*(m*(p:ℝ)^2+m*D*(p:ℝ)^3))=
    -(1-τ)^2*m*(p:ℝ)^2/(2*(1+(D:ℝ)*(p:ℝ)))
  have hden : 0<1+(D:ℝ)*(p:ℝ) := by positivity
  have hden' : 0 < m*(p:ℝ)^2+m*D*(p:ℝ)^3 := by
    have hh : 0 ≤ m*(D:ℝ)*(p:ℝ)^3 := by positivity
    linarith
  field_simp [hm0,hp0,hden.ne',hden'.ne']

theorem finite_graph_janson_fraction_restricted (W : Finset V) (G : SimpleGraph W)
    (p : unitInterval) {D : ℕ}
    (hD : ∀ v w, G.Adj v w → G.degree v+G.degree w≤D+2)
    {τ : ℝ} (hτ0 : 0≤τ) (hτ1 : τ≤1) :
    (subsetBernoulli W p).prob (fun S => (sampledEdgeCount G {v : W | v.val∈S}:ℝ)≤
      τ*(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2) ≤
    exp (-(1-τ)^2*(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2/(2*(1+(D:ℝ)*(p:ℝ)))) := by
  rw [subsetBernoulli_prob_subtype]
  have he : ∀ S : Finset W,
      {v : W | v.val∈S.map (Function.Embedding.subtype (·∈W))}=(S:Set W) := by
    intro S; ext v; simp
  simp_rw [he]
  exact finite_graph_janson_fraction G p hD hτ0 hτ1

end
end Cycle13
