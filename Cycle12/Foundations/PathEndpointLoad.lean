import Cycle12.Foundations.RoutingLoadCounts
import Cycle12.Foundations.Definitions

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem endpointLoad_eq_incident_card (a b : I → V) (hne : ∀ i,a i ≠ b i) (v : V) :
    endpointLoad a b v=(univ.filter fun i => a i=v ∨ b i=v).card := by
  have hd : Disjoint (univ.filter fun i => a i=v) (univ.filter fun i => b i=v) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hne i ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  rw [endpointLoad,← Finset.card_union_of_disjoint hd]
  congr 1
  ext i
  simp

theorem walk_endpoint_neighbor {G : SimpleGraph V} {a b v : V}
    (p : G.Walk a b) (hne : a ≠ b) (hv : a=v ∨ b=v) :
    ∃ w,G.Adj v w ∧ s(v,w)∈p.edgeSet := by
  rcases hv with rfl | rfl
  · exact ⟨p.snd,p.adj_snd (Walk.not_nil_of_ne hne),
      p.mk_start_snd_mem_edges (Walk.not_nil_of_ne hne)⟩
  · refine ⟨p.reverse.snd,p.reverse.adj_snd (Walk.not_nil_of_ne hne.symm),?_⟩
    have hh := p.reverse.mk_start_snd_mem_edges (Walk.not_nil_of_ne hne.symm)
    simpa using hh

/-- Endpoint occurrences inject into distinct original incident edges.
The degree bound is for the entire original graph, hence remains valid
when the indexed family aggregates paths from arbitrarily many batches. -/
theorem endpointLoad_le_original_degree (G : SimpleGraph V) (a b : I → V)
    (p : ∀ i,G.Walk (a i) (b i)) (hne : ∀ i,a i ≠ b i)
    (hd : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet)) (v : V) :
    endpointLoad a b v ≤ G.degree v := by
  let S : Finset I := univ.filter fun i => a i=v ∨ b i=v
  have hex : ∀ i : S,∃ w,G.Adj v w ∧ s(v,w)∈(p i.val).edgeSet := by
    intro i
    exact walk_endpoint_neighbor (p i.val) (hne i.val) (mem_filter.mp i.property).2
  choose next hadj hmem using hex
  let f : S → G.neighborSet v := fun i => ⟨next i,hadj i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hneij
    have he : next i=next j := congrArg Subtype.val hij
    have hn : i.val ≠ j.val := fun h => hneij (Subtype.ext h)
    exact Set.disjoint_left.mp (hd hn) (hmem i) (by simpa only [he] using hmem j)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe,SimpleGraph.card_neighborSet_eq_degree] at hc
  rw [endpointLoad_eq_incident_card a b hne v]
  exact hc

end
end Cycle13
