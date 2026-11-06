import Cycle12.Foundations.ForestBound

namespace Cycle13
open SimpleGraph Finset
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem finset_symmDiff_card_balance [DecidableEq V] (A B : Finset V) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hdisj : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp hv).2 (mem_sdiff.mp hw).1
  rw [symmDiff_def, sup_eq_union, card_union_of_disjoint hdisj]
  have h₁ := card_sdiff_add_card_inter A B
  have h₂ := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at h₂
  omega

theorem graph_symmDiff_degree_balance (G H : SimpleGraph V) (v : V) :
    (G ∆ H).degree v + 2 * (G ⊓ H).degree v = G.degree v + H.degree v := by
  classical
  have he : (G ∆ H).neighborFinset v = G.neighborFinset v ∆ H.neighborFinset v := by
    apply Finset.coe_injective
    simp only [Finset.coe_symmDiff, coe_neighborFinset]
    ext w
    simp [symmDiff_def, SimpleGraph.neighborSet]
  simp only [← card_neighborFinset_eq_degree, neighborFinset_inf]
  rw [he]
  exact finset_symmDiff_card_balance _ _

theorem graph_symmDiff_degree_even (G H : SimpleGraph V) (v : V) :
    Even ((G ∆ H).degree v) ↔ (Even (G.degree v) ↔ Even (H.degree v)) := by
  have h := graph_symmDiff_degree_balance G H v
  simp only [Nat.even_iff]
  omega

def walkEdgeGraph {G : SimpleGraph V} {x y : V} (p : G.Walk x y) : SimpleGraph V :=
  p.toSubgraph.spanningCoe

theorem walkEdgeGraph_edges {G : SimpleGraph V} {x y : V} (p : G.Walk x y) :
    (walkEdgeGraph p).edgeSet = p.edgeSet := by
  simp [walkEdgeGraph]

theorem walkEdgeGraph_le {G : SimpleGraph V} {x y : V} (p : G.Walk x y) :
    walkEdgeGraph p ≤ G := p.toSubgraph.spanningCoe_le

theorem path_edge_graph_even_degree {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hne : x ≠ y) (v : V) :
    Even ((walkEdgeGraph p).degree v) ↔ v ≠ x ∧ v ≠ y := by
  let q := p.transfer (walkEdgeGraph p) (by
    intro e he
    rw [walkEdgeGraph_edges]
    exact he)
  have hq : q.IsTrail := hp.isTrail.transfer _
  have he : q.edgeSet = (walkEdgeGraph p).edgeSet := by
    simp only [q, Walk.edgeSet_transfer, walkEdgeGraph_edges]
  have hu : q.IsEulerian := hq.isEulerian_iff.mpr he
  exact (hu.even_degree_iff (x := v)).trans ⟨fun h => h hne, fun h _ => h⟩

end
end Cycle13
