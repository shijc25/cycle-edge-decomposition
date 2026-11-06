import Cycle12.Foundations.Definitions

/-! The matching step in the DeVos vertex-splitting argument: unmatched
neighbors form a clique, and hence at most `t-2` neighbors remain unmatched. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem exists_maximal_matching (G : SimpleGraph V) :
    ∃ M : G.Subgraph, Maximal (fun N => N.IsMatching) M := by
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simpa using hv
  obtain ⟨M, _, hM⟩ := Finite.exists_le_maximal hbot
  exact ⟨M, hM⟩

theorem maximal_matching_unmatched_nonadjacent (G : SimpleGraph V) (M : G.Subgraph)
    (hM : Maximal (fun N => N.IsMatching) M) {u v : V}
    (hu : u ∉ M.verts) (hv : v ∉ M.verts) : ¬G.Adj u v := by
  intro hadj
  let E := G.subgraphOfAdj hadj
  have hE : E.IsMatching := Subgraph.IsMatching.subgraphOfAdj hadj
  have hd : Disjoint M.support E.support := by
    apply Set.disjoint_left.mpr
    intro x hx hxe
    have hxv := M.support_subset_verts hx
    have hxs : x ∈ ({u,v} : Set V) := by
      simpa only [E, SimpleGraph.support_subgraphOfAdj] using hxe
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxs
    rcases hxs with rfl | rfl
    · exact hu hxv
    · exact hv hxv
  have hsup : (M ⊔ E).IsMatching := hM.prop.sup hE hd
  have hle : M ⊔ E ≤ M := hM.2 hsup le_sup_left
  have huE : u ∈ E.verts := by simp [E, subgraphOfAdj_verts]
  exact hu (hle.1 (Or.inr huE))

theorem clique_ncard_lt_of_cliqueFree (G : SimpleGraph V) {t : ℕ}
    (hfree : G.CliqueFree t) {s : Set V} (hs : G.IsClique s) : s.ncard < t := by
  classical
  by_contra h
  have ht : t ≤ s.toFinset.card := by
    simpa only [Set.ncard_eq_toFinset_card'] using le_of_not_gt h
  obtain ⟨a, has, hac⟩ := Finset.exists_subset_card_eq ht
  apply hfree a
  refine ⟨hs.subset ?_, hac⟩
  intro x hx
  exact Set.mem_toFinset.mp (has hx)

theorem neighbor_matching_unmatched_bound (G : SimpleGraph V) (u : V) {t : ℕ}
    (ht : 2 ≤ t) (hfree : G.CliqueFree t)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph)
    (hM : Maximal (fun N => N.IsMatching) M) :
    (M.vertsᶜ : Set (G.neighborSet u)).ncard ≤ t - 2 := by
  classical
  let X : Set (G.neighborSet u) := M.vertsᶜ
  let S : Set V := Subtype.val '' X
  have hS : G.IsClique S := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hab
    by_contra hnot
    have hcom : ((G.induce (G.neighborSet u))ᶜ).Adj a b := by
      exact ⟨fun he => hab (congrArg Subtype.val he), hnot⟩
    exact maximal_matching_unmatched_nonadjacent _ M hM ha hb hcom
  have huS : u ∉ S := by
    rintro ⟨a, _, ha⟩
    exact G.irrefl (ha ▸ a.2)
  have hcl : G.IsClique (insert u S) := hS.insert (by
    rintro b ⟨a, ha, rfl⟩ _
    exact a.2)
  have hcard := clique_ncard_lt_of_cliqueFree G hfree hcl
  rw [Set.ncard_insert_of_notMem huS] at hcard
  have hSsize : S.ncard = X.ncard := Set.ncard_image_of_injective X Subtype.val_injective
  rw [hSsize] at hcard
  change X.ncard ≤ t - 2
  omega

theorem exists_neighbor_matching (G : SimpleGraph V) (u : V) {t : ℕ}
    (ht : 2 ≤ t) (hfree : G.CliqueFree t) :
    ∃ M : ((G.induce (G.neighborSet u))ᶜ).Subgraph,
      M.IsMatching ∧ (M.vertsᶜ : Set (G.neighborSet u)).ncard ≤ t - 2 := by
  obtain ⟨M, hM⟩ := exists_maximal_matching ((G.induce (G.neighborSet u))ᶜ)
  exact ⟨M, hM.prop, neighbor_matching_unmatched_bound G u ht hfree M hM⟩

theorem matching_matched_vertices_card (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have hdegrees : ∀ v : M.verts, M.coe.degree v = 1 := by
    intro v
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    obtain ⟨w, hw, huniq⟩ := hM v.2
    refine ⟨⟨w, hw.snd_mem⟩, hw, ?_⟩
    intro y hy
    exact Subtype.ext (huniq y.1 hy)
  have hsum := M.coe.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hdegrees hsum
  simp only [hdegrees, sum_const, card_univ, smul_eq_mul, mul_one] at hsum
  have hedge : M.coe.edgeFinset.card = M.edgeSet.ncard := by
    rw [← M.image_coe_edgeSet_coe,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    simp only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  rw [hedge] at hsum
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using hsum

theorem neighbor_matching_degree_balance (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) (hM : M.IsMatching) :
    2 * M.edgeSet.ncard + (M.vertsᶜ : Set (G.neighborSet u)).ncard = G.degree u := by
  rw [← matching_matched_vertices_card _ M hM, Set.ncard_add_ncard_compl]
  simp only [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

end
end Cycle13
