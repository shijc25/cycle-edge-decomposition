import Cycle12.Foundations.SubsetBernoulliTransport
import Cycle12.Foundations.GraphJanson

/-! Janson's theorem in the same finite laws used by the marking
experiment, including a graph on the unmarked vertices. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem finite_graph_janson (G : SimpleGraph V) (p : unitInterval) {D : ℕ}
    (hD : ∀ v w, G.Adj v w → G.degree v+G.degree w ≤ D+2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2) :
    (bernoulliSubset (V:=V) p).prob (fun S =>
      (sampledEdgeCount G (S:Set V):ℝ) ≤ (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2-t) ≤
    Real.exp (-t^2/(2*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
      (Fintype.card G.edgeSet:ℝ)*D*(p:ℝ)^3))) := by
  rw [bernoulliSubset_prob_eq_setBernoulli p
    (fun S : Set V => (sampledEdgeCount G S:ℝ) ≤ (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2-t)]
  exact vertex_sample_edge_lower_tail G p hD ht0 ht

theorem finite_graph_janson_restricted (W : Finset V) (G : SimpleGraph W)
    (p : unitInterval) {D : ℕ}
    (hD : ∀ v w, G.Adj v w → G.degree v+G.degree w ≤ D+2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2) :
    (subsetBernoulli W p).prob (fun S =>
      (sampledEdgeCount G {v : W | v.val∈S}:ℝ) ≤ (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2-t) ≤
    Real.exp (-t^2/(2*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
      (Fintype.card G.edgeSet:ℝ)*D*(p:ℝ)^3))) := by
  rw [subsetBernoulli_prob_subtype]
  have he : ∀ S : Finset W,
      {v : W | v.val∈S.map (Function.Embedding.subtype (·∈W))}=(S:Set W) := by
    intro S; ext v; simp
  simp_rw [he]
  exact finite_graph_janson G p hD ht0 ht

end
end Cycle13
