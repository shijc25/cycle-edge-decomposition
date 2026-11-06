import Cycle12.Foundations.VertexSplitting
import Cycle12.Foundations.ImmersionPaths

namespace Cycle13
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem splitSupplement_adj_properties (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) {x y : V}
    (h : (splitSupplement G u M).Adj x y) :
    G.Adj u x ∧ G.Adj u y ∧ ¬G.Adj x y := by
  rw [splitSupplement, SimpleGraph.map_adj] at h
  obtain ⟨a, b, hab, rfl, rfl⟩ := h
  exact ⟨a.2, b.2, (M.adj_sub hab).2⟩

theorem splitSupplement_matching (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching)
    {x y z : V} (hxy : (splitSupplement G u M).Adj x y)
    (hxz : (splitSupplement G u M).Adj x z) : y = z := by
  rw [splitSupplement, SimpleGraph.map_adj] at hxy hxz
  obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
  obtain ⟨c, d, hcd, hc, hd⟩ := hxz
  have hca : c = a := Subtype.ext hc
  subst c
  have hbd := hM.eq_of_adj_left hab hcd
  exact (congrArg Subtype.val hbd).trans hd

theorem matching_edges_eq_of_common_vertex (H : SimpleGraph V)
    (hunique : ∀ {x y z : V}, H.Adj x y → H.Adj x z → y = z)
    {x y a b z : V} (hxy : H.Adj x y) (hab : H.Adj a b)
    (hz : z ∈ s(x,y)) (hz' : z ∈ s(a,b)) : s(x,y) = s(a,b) := by
  rcases Sym2.mem_iff.mp hz with rfl | rfl
  · rcases Sym2.mem_iff.mp hz' with rfl | rfl
    · rw [hunique hxy hab]
    · rw [hunique hxy hab.symm]
      exact Sym2.eq_swap
  · rcases Sym2.mem_iff.mp hz' with rfl | rfl
    · rw [hunique hxy.symm hab]
      exact Sym2.eq_swap
    · rw [hunique hxy.symm hab.symm]

def splitEdgeRoute (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph)
    {x y : ({u}ᶜ : Set V)} (h : (splitGraph G u M).Adj x y) : G.Walk x.1 y.1 :=
  if hG : G.Adj x.1 y.1 then hG.toWalk else
    let hs : (splitSupplement G u M).Adj x.1 y.1 := h.resolve_left hG
    let hm := splitSupplement_adj_properties G u M hs
    Walk.cons hm.1.symm (Walk.cons hm.2.1 Walk.nil)

theorem splitEdgeRoute_edge_origin (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph)
    {x y : ({u}ᶜ : Set V)} (h : (splitGraph G u M).Adj x y)
    {e : Sym2 V} (he : e ∈ (splitEdgeRoute G u M h).edgeSet) :
    (G.Adj x.1 y.1 ∧ e = s(x.1,y.1)) ∨
    ((splitSupplement G u M).Adj x.1 y.1 ∧ ∃ z, z ∈ s(x.1,y.1) ∧ e = s(u,z)) := by
  by_cases hG : G.Adj x.1 y.1
  · exact Or.inl ⟨hG, by simpa [splitEdgeRoute, hG, Adj.toWalk] using he⟩
  · have hs : (splitSupplement G u M).Adj x.1 y.1 := h.resolve_left hG
    refine Or.inr ⟨hs, ?_⟩
    have he' : e = s(x.1,u) ∨ e = s(u,y.1) := by simpa [splitEdgeRoute, hG] using he
    rcases he' with he | he
    · exact ⟨x.1, by simp, he.trans Sym2.eq_swap⟩
    · exact ⟨y.1, by simp, he⟩

theorem splitEdgeRoute_avoids (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph)
    {x y : ({u}ᶜ : Set V)} (h : (splitGraph G u M).Adj x y)
    (z : ({u}ᶜ : Set V)) (hz : z.1 ∈ (splitEdgeRoute G u M h).support) :
    z = x ∨ z = y := by
  have hzu : z.1 ≠ u := z.2
  by_cases hG : G.Adj x.1 y.1
  · have hz' : z.1 = x.1 ∨ z.1 = y.1 := by simpa [splitEdgeRoute, hG, Adj.toWalk] using hz
    exact hz'.imp Subtype.ext Subtype.ext
  · have hz' : z.1 = x.1 ∨ z.1 = u ∨ z.1 = y.1 := by simpa [splitEdgeRoute, hG] using hz
    rcases hz' with hx | hu | hy
    · exact Or.inl (Subtype.ext hx)
    · exact (hzu hu).elim
    · exact Or.inr (Subtype.ext hy)

theorem splitEdgeRoute_disjoint (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching)
    {x y a b : ({u}ᶜ : Set V)} (hxy : (splitGraph G u M).Adj x y)
    (hab : (splitGraph G u M).Adj a b) (hne : s(x,y) ≠ s(a,b)) :
    Disjoint (splitEdgeRoute G u M hxy).edgeSet (splitEdgeRoute G u M hab).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he1 he2
  have hneq : s(x.1,y.1) ≠ s(a.1,b.1) := by
    intro he
    exact hne (Sym2.map.injective Subtype.val_injective he)
  have hxu : u ∉ s(x.1,y.1) := by
    simp only [Sym2.mem_iff, not_or]
    exact ⟨Ne.symm x.2, Ne.symm y.2⟩
  have hau : u ∉ s(a.1,b.1) := by
    simp only [Sym2.mem_iff, not_or]
    exact ⟨Ne.symm a.2, Ne.symm b.2⟩
  rcases splitEdgeRoute_edge_origin G u M hxy he1 with ⟨hG1, he1⟩ | ⟨hS1, z, hz, he1⟩
  · rcases splitEdgeRoute_edge_origin G u M hab he2 with ⟨hG2, he2⟩ | ⟨hS2, w, hw, he2⟩
    · exact hneq (he1.symm.trans he2)
    · exact hxu ((he1.symm.trans he2).symm ▸ Sym2.mem_mk_left u w)
  · rcases splitEdgeRoute_edge_origin G u M hab he2 with ⟨hG2, he2⟩ | ⟨hS2, w, hw, he2⟩
    · exact hau ((he2.symm.trans he1).symm ▸ Sym2.mem_mk_left u z)
    · have hzw : z = w := Sym2.congr_right.mp (he1.symm.trans he2)
      subst w
      exact hneq (matching_edges_eq_of_common_vertex (splitSupplement G u M)
        (splitSupplement_matching G u M hM) hS1 hS2 hz hw)

def vertexSplitRouting (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching) :
    EdgeRouting (splitGraph G u M) G where
  vertex := Function.Embedding.subtype (· ∈ ({u}ᶜ : Set V))
  route := splitEdgeRoute G u M
  disjoint := splitEdgeRoute_disjoint G u M hM
  avoids := splitEdgeRoute_avoids G u M

theorem strong_clique_lifts_through_split (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching) {t : ℕ}
    (h : Nonempty (StrongCliqueImmersion t (splitGraph G u M))) :
    Nonempty (StrongCliqueImmersion t G) :=
  ⟨h.some.lift (vertexSplitRouting G u M hM)⟩

end
end Cycle13
