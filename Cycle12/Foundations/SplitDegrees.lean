import Cycle12.Foundations.SplitRouting

/-! Pointwise degree accounting for simple-graph splitting by a neighbour
complement matching, including one prescribed unmatched neighbour. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem delete_vertex_degree_balance (G : SimpleGraph V) (u : V) (v : ({u}ᶜ : Set V)) :
    (G.induce {u}ᶜ).degree v+(if G.Adj v.val u then 1 else 0)=G.degree v.val := by
  have he : Subtype.val '' ((G.induce {u}ᶜ).neighborSet v)=G.neighborSet v.val\{u} := by
    ext w
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hx,x.property⟩
    · rintro ⟨hw,hne⟩
      exact ⟨⟨w,hne⟩,hw,rfl⟩
  simp only [← ncard_neighborSet]
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective,he]
  by_cases hu : G.Adj v.val u
  · rw [if_pos hu]
    exact Set.ncard_sdiff_singleton_add_one hu
  · rw [if_neg hu,Nat.add_zero]
    rw [Set.sdiff_singleton_eq_self (show u∉G.neighborSet v.val from hu)]

theorem splitSupplement_degree (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching) (v : V) :
    (splitSupplement G u M).degree v=
      if ∃ a : G.neighborSet u, a∈M.verts ∧ a.val=v then 1 else 0 := by
  classical
  split_ifs with hv
  · obtain ⟨a,ha,rfl⟩ := hv
    apply degree_eq_one_iff_existsUnique_adj.mpr
    obtain ⟨b,hab,hunique⟩ := hM ha
    have hsup : (splitSupplement G u M).Adj a.val b.val := by
      exact SimpleGraph.map_adj_apply.mpr hab
    exact ⟨b.val,hsup,fun w hw => splitSupplement_matching G u M hM hw hsup⟩
  · rw [← ncard_neighborSet]
    apply (Set.ncard_eq_zero (Set.toFinite _)).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    change (splitSupplement G u M).Adj v w at hw
    rw [splitSupplement,SimpleGraph.map_adj] at hw
    obtain ⟨a,b,hab,hav,hbw⟩ := hw
    exact hv ⟨a,M.edge_vert hab,hav⟩

theorem split_degree_balance (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (v : ({u}ᶜ : Set V)) :
    (splitGraph G u M).degree v+(if G.Adj u v.val then 1 else 0)=
      G.degree v.val+(splitSupplement G u M).degree v.val := by
  have hd := delete_vertex_degree_balance (G⊔splitSupplement G u M) u v
  have ha : (G⊔splitSupplement G u M).Adj v.val u ↔ G.Adj u v.val := by
    simp only [sup_adj]
    have hn : ¬(splitSupplement G u M).Adj v.val u := fun h =>
      splitSupplement_not_adj_pivot G u v.val M h.symm
    rw [or_iff_left hn]
    exact G.adj_comm _ _
  have hdis : Disjoint (G.neighborSet v.val) ((splitSupplement G u M).neighborSet v.val) := by
    apply Set.disjoint_left.mpr
    intro w hG hS
    exact (splitSupplement_adj_properties G u M hS).2.2 hG
  have he : (G⊔splitSupplement G u M).neighborSet v.val=
      G.neighborSet v.val∪(splitSupplement G u M).neighborSet v.val := rfl
  simp only [← ncard_neighborSet] at hd ⊢
  simp only [ha] at hd
  rw [he,Set.ncard_union_eq hdis] at hd
  exact hd

theorem split_degree_bounds (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching)
    (v : ({u}ᶜ : Set V)) :
    (splitGraph G u M).degree v ≤ G.degree v.val ∧
      G.degree v.val ≤ (splitGraph G u M).degree v+1 := by
  have hb := split_degree_balance G u M v
  have hs := splitSupplement_degree G u M hM v.val
  simp only [← ncard_neighborSet] at hb hs ⊢
  by_cases ha : G.Adj u v.val
  · rw [if_pos ha] at hb
    split_ifs at hs <;> omega
  · have hn : ¬∃ a : G.neighborSet u, a∈M.verts ∧ a.val=v.val := by
      rintro ⟨a,hm,hav⟩
      exact ha (hav ▸ a.property)
    rw [if_neg ha] at hb
    rw [if_neg hn] at hs
    omega

theorem split_degree_eq_of_covered (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching)
    (v : ({u}ᶜ : Set V))
    (hc : ∀ a : G.neighborSet u, a.val=v.val → a∈M.verts) :
    (splitGraph G u M).degree v=G.degree v.val := by
  have hb := split_degree_balance G u M v
  have hs := splitSupplement_degree G u M hM v.val
  simp only [← ncard_neighborSet] at hb hs ⊢
  by_cases ha : G.Adj u v.val
  · have hm : ∃ a : G.neighborSet u, a∈M.verts ∧ a.val=v.val :=
      ⟨⟨v.val,ha⟩,hc ⟨v.val,ha⟩ rfl,rfl⟩
    rw [if_pos ha] at hb
    rw [if_pos hm] at hs
    omega
  · have hn : ¬∃ a : G.neighborSet u, a∈M.verts ∧ a.val=v.val := by
      rintro ⟨a,hm,hav⟩
      exact ha (hav ▸ a.property)
    rw [if_neg ha] at hb
    rw [if_neg hn] at hs
    omega

theorem split_adj_iff_of_not_neighbor (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph)
    (x y : ({u}ᶜ : Set V)) (hx : ¬G.Adj u x.val) :
    (splitGraph G u M).Adj x y ↔ G.Adj x.val y.val := by
  change (G.Adj x.val y.val ∨ (splitSupplement G u M).Adj x.val y.val) ↔ _
  exact or_iff_left (fun h => hx (splitSupplement_adj_properties G u M h).1)

theorem split_degree_eq_of_not_neighbor (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching)
    (v : ({u}ᶜ : Set V)) (hv : ¬G.Adj u v.val) :
    (splitGraph G u M).degree v=G.degree v.val := by
  apply split_degree_eq_of_covered G u M hM v
  intro a ha
  exact (hv (ha ▸ a.property)).elim

end
end Cycle13
