import Cycle12.Foundations.SplittingMatching

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

def splitSupplement (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) : SimpleGraph V :=
  M.spanningCoe.map (Function.Embedding.subtype (· ∈ G.neighborSet u))

def splitGraph (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) : SimpleGraph ({u}ᶜ : Set V) :=
  (G ⊔ splitSupplement G u M).induce {u}ᶜ

theorem splitSupplement_edges (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) :
    (splitSupplement G u M).edgeSet = Sym2.map Subtype.val '' M.edgeSet := by
  rw [splitSupplement, SimpleGraph.edgeSet_map, Subgraph.edgeSet_spanningCoe]
  rfl

theorem splitSupplement_disjoint (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) :
    Disjoint G.edgeSet (splitSupplement G u M).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e heG heM
  rw [splitSupplement_edges] at heM
  obtain ⟨d, hd, rfl⟩ := heM
  induction d using Sym2.ind with
  | _ x y => exact (M.adj_sub hd).2 heG

theorem splitSupplement_not_adj_pivot (G : SimpleGraph V) (u v : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) :
    ¬(splitSupplement G u M).Adj u v := by
  rw [splitSupplement, SimpleGraph.map_adj]
  rintro ⟨x, y, hxy, hx, hy⟩
  change x.1 = u at hx
  exact G.irrefl (hx ▸ x.2)

theorem split_degree_at_pivot (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) :
    (G ⊔ splitSupplement G u M).degree u = G.degree u := by
  have hn : (G ⊔ splitSupplement G u M).neighborSet u = G.neighborSet u := by
    ext v
    simp only [mem_neighborSet, sup_adj, splitSupplement_not_adj_pivot, or_false]
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  rw [hn]

theorem split_augmented_edge_count (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) :
    (G ⊔ splitSupplement G u M).edgeSet.ncard = G.edgeSet.ncard + M.edgeSet.ncard := by
  rw [edgeSet_sup, Set.ncard_union_eq (splitSupplement_disjoint G u M),
    splitSupplement_edges, Set.ncard_image_of_injective _
      (Sym2.map.injective Subtype.val_injective)]

theorem delete_vertex_edge_balance (G : SimpleGraph V) (u : V) :
    (G.induce {u}ᶜ).edgeSet.ncard + G.degree u = G.edgeSet.ncard := by
  classical
  have h := G.card_edgeFinset_induce_compl_singleton u
  rw [G.card_edgeFinset_deleteIncidenceSet] at h
  have hh := congrArg (fun k => k + G.degree u) h
  rw [Nat.sub_add_cancel (G.degree_le_card_edgeFinset u)] at hh
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hh

theorem split_edge_balance (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) :
    (splitGraph G u M).edgeSet.ncard + G.degree u = G.edgeSet.ncard + M.edgeSet.ncard := by
  have h := delete_vertex_edge_balance (G ⊔ splitSupplement G u M) u
  have hd := split_degree_at_pivot G u M
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hd ⊢
  rw [hd, split_augmented_edge_count] at h
  exact h

theorem split_order (G : SimpleGraph V) (u : V)
    (M : ((G.induce (G.neighborSet u))ᶜ).Subgraph) :
    Fintype.card ({u}ᶜ : Set V) = Fintype.card V - 1 := by
  classical
  rw [Fintype.card_compl_set]
  simp

/-- The precise one-step average-degree estimate from the matching construction.
The path realization and iteration to a strong immersion are separate theorems. -/
theorem exists_split_average_bound (G : SimpleGraph V) (u : V) {t : ℕ}
    (ht : 2 ≤ t) (hfree : G.CliqueFree t) (hn : 1 < Fintype.card V)
    (hu : (G.degree u : ℝ) ≤ 2 * G.edgeSet.ncard / Fintype.card V) :
    ∃ M : ((G.induce (G.neighborSet u))ᶜ).Subgraph, M.IsMatching ∧
      2 * ((splitGraph G u M).edgeSet.ncard : ℝ) / ((Fintype.card V : ℝ) - 1) ≥
        2 * (G.edgeSet.ncard : ℝ) / Fintype.card V -
          ((t : ℝ) - 2) / ((Fintype.card V : ℝ) - 1) := by
  obtain ⟨M, hM, hX⟩ := exists_neighbor_matching G u ht hfree
  have he := split_edge_balance G u M
  have hd := neighbor_matching_degree_balance G u M hM
  have heR : ((splitGraph G u M).edgeSet.ncard : ℝ) + G.degree u =
      G.edgeSet.ncard + (M.edgeSet.ncard : ℝ) := by exact_mod_cast he
  have hdR : 2 * (M.edgeSet.ncard : ℝ) +
      (M.vertsᶜ : Set (G.neighborSet u)).ncard = G.degree u := by exact_mod_cast hd
  have hXR : ((M.vertsᶜ : Set (G.neighborSet u)).ncard : ℝ) ≤ (t : ℝ) - 2 := by
    exact_mod_cast hX
  have hnR : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hden : (0 : ℝ) < Fintype.card V - 1 := by linarith
  have horder : (0 : ℝ) < Fintype.card V := by linarith
  have hlow := (le_div_iff₀ horder).mp hu
  refine ⟨M, hM, ?_⟩
  apply (le_div_iff₀ hden).mpr
  have hcancel : (2 * (G.edgeSet.ncard : ℝ) / Fintype.card V) * Fintype.card V =
      2 * G.edgeSet.ncard := by field_simp
  have hcancel' : (((t : ℝ) - 2) / ((Fintype.card V : ℝ) - 1)) *
      ((Fintype.card V : ℝ) - 1) = (t : ℝ) - 2 := by field_simp
  nlinarith

end
end Cycle13
