import Cycle12.Foundations.EulerCyclePacking

namespace Cycle13
open SimpleGraph Finset
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem parity_delete_closed_trail {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsTrail) (u : V) :
    Even ((G.deleteEdges p.edgeSet).degree u) ↔ Even (G.degree u) := by
  have hgraph : G.deleteEdges p.edgeSet=G ∆ walkEdgeGraph p := by
    rw [symmDiff_of_ge (walkEdgeGraph_le p)]
    apply SimpleGraph.edgeSet_injective
    simp only [SimpleGraph.edgeSet_deleteEdges,SimpleGraph.edgeSet_sdiff,walkEdgeGraph_edges]
  have hx := graph_symmDiff_degree_even G (walkEdgeGraph p) u
  have he := closed_trail_edge_graph_even p hp u
  have hh : Even ((G ∆ walkEdgeGraph p).degree u) ↔ Even (G.degree u) := by tauto
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
  simpa only [hgraph] using hh

/-- Removing cycles from a parity correction preserves all degree
parities and only decreases degrees. A minimum-edge correction is a forest. -/
theorem exists_acyclic_parity_subgraph (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      ∀ v, Even (F.degree v) ↔ Even (G.degree v) := by
  let good (n : ℕ) : Prop := ∃ F : SimpleGraph V,
    F ≤ G ∧ F.edgeSet.ncard=n ∧ ∀ v, Even (F.degree v) ↔ Even (G.degree v)
  have hex : ∃ n, good n := ⟨G.edgeSet.ncard,G,le_rfl,rfl,fun _ => Iff.rfl⟩
  obtain ⟨F,hFG,hFn,hpar⟩ := Nat.find_spec hex
  refine ⟨F,hFG,?_,hpar⟩
  intro v p hp
  let H := F.deleteEdges p.edgeSet
  have hHF : H ≤ F := fun _ _ h => h.1
  have hcount : H.edgeSet.ncard+p.length=F.edgeSet.ncard := by
    rw [show H.edgeSet=F.edgeSet\p.edgeSet from SimpleGraph.edgeSet_deleteEdges p.edgeSet]
    rw [← cycle_edgeSet_ncard hp]
    exact Set.ncard_sdiff_add_ncard_of_subset p.edges_subset_edgeSet
  have hsmall : H.edgeSet.ncard < Nat.find hex := by
    have hlen := hp.three_le_length
    omega
  have hgood : good H.edgeSet.ncard := by
    refine ⟨H,hHF.trans hFG,rfl,fun u => ?_⟩
    have hh := (parity_delete_closed_trail p hp.isTrail u).trans (hpar u)
    simpa only [← ncard_neighborSet] using hh
  exact Nat.find_min hex hsmall hgood

end
end Cycle13
