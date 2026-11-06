import Cycle12.Foundations.EulerCyclePacking

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

namespace CyclePacking
variable {G : SimpleGraph V} {H : SimpleGraph W}

def mapInjectiveHom (P : CyclePacking G) (f : G →g H) (hf : Function.Injective f) : CyclePacking H where
  count := P.count
  parts i := Sym2.map f '' P.parts i
  cycles i := by
    obtain ⟨v,p,hp,he⟩ := P.cycles i
    exact ⟨f v,p.map f,hp.map hf,by rw [he,Walk.edgeSet_map]⟩
  disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro e ⟨a,ha,hea⟩ ⟨b,hb,heb⟩
    have he := (Sym2.map.injective hf) (hea.trans heb.symm)
    subst b
    exact Set.disjoint_left.mp (P.disjoint hij) ha hb

theorem used_mapInjectiveHom (P : CyclePacking G) (f : G →g H) (hf : Function.Injective f) :
    (P.mapInjectiveHom f hf).used=Sym2.map f '' P.used := by
  simp only [used,mapInjectiveHom,Set.image_iUnion]

theorem used_eq_of_singles_zero (P : CyclePacking G) (hP : P.singles=0) : P.used=G.edgeSet := by
  have hz : P.residue.edgeSet=∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hP
  rw [residue,SimpleGraph.edgeSet_deleteEdges] at hz
  exact Set.Subset.antisymm P.used_subset (Set.diff_eq_empty.mp hz)

end CyclePacking

theorem trail_edgeSet_ncard {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    p.edgeSet.ncard=p.length := by
  rw [← p.coe_edges_toFinset,Set.ncard_coe_finset,List.toFinset_card_of_nodup hp.edges_nodup]
  exact p.length_edges

/-- A closed trail is partitioned into actual edge-disjoint simple
cycles, with at most m-n+1 cycles on its visited vertices. Equivalently,
apart from the initial cycle, each extra cycle is paid by a repeated
vertex in the cyclic vertex sequence. -/
theorem closed_trail_cycle_decomposition {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsTrail) :
    ∃ P : CyclePacking G, P.used=p.edgeSet ∧
      P.count+p.support.toFinset.card ≤ p.length+1 := by
  let H := p.toSubgraph.coe
  have hconn : H.Connected := p.toSubgraph_connected.coe
  have heven : ∀ x, Even (Nat.card (H.neighborSet x)) := by
    intro x
    have he := closed_trail_edge_graph_even p hp x.val
    have hc : Nat.card (H.neighborSet x)=Nat.card ((walkEdgeGraph p).neighborSet x.val) :=
      Nat.card_congr (p.toSubgraph.coeNeighborSetEquiv x)
    rw [hc]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he
  obtain ⟨Q,hQ,hcount⟩ := connected_even_cycle_decomposition H hconn (by
    intro x
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heven x)
  let f : H →g G := p.toSubgraph.hom
  have hf : Function.Injective f := Subtype.val_injective
  let P := Q.mapInjectiveHom f hf
  have hHedges : Sym2.map f '' H.edgeSet=p.edgeSet := by
    change Sym2.map (Subtype.val : p.toSubgraph.verts → V) '' p.toSubgraph.coe.edgeSet=p.edgeSet
    rw [SimpleGraph.Subgraph.image_coe_edgeSet_coe]
    ext e
    exact p.mem_edges_toSubgraph
  have hused : P.used=p.edgeSet := by
    rw [CyclePacking.used_mapInjectiveHom,Q.used_eq_of_singles_zero hQ]
    exact hHedges
  have horder : Fintype.card p.toSubgraph.verts=p.support.toFinset.card := by
    apply Fintype.card_of_finset' p.support.toFinset
    intro x
    simp [p.mem_verts_toSubgraph]
  have hedges : H.edgeSet.ncard=p.length := by
    have hh := congrArg Set.ncard hHedges
    rw [Set.ncard_image_of_injective _ (Sym2.map.injective hf),trail_edgeSet_ncard p hp] at hh
    exact hh
  refine ⟨P,hused,?_⟩
  change Q.count+p.support.toFinset.card ≤ p.length+1
  simpa only [horder,hedges] using hcount

end
end Cycle13
