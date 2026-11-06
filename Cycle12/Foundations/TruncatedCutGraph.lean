import Cycle12.Foundations.SamplingGeometry

/-! An actual cut subgraph obtained by capping the degree on one side.
The choice depends only on the graph, the cut, and the integer cap. -/
namespace Cycle13
open Finset SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def cutChoices (G : SimpleGraph V) (S : Finset V) (k : ℕ) (v : V) : Finset V :=
  Classical.choose (exists_subset_card_eq (min_le_right k (neighborsIn G v Sᶜ).card))

theorem cutChoices_subset (G : SimpleGraph V) (S : Finset V) (k : ℕ) (v : V) :
    cutChoices G S k v⊆neighborsIn G v Sᶜ :=
  (Classical.choose_spec (exists_subset_card_eq (min_le_right k (neighborsIn G v Sᶜ).card))).1

theorem cutChoices_card (G : SimpleGraph V) (S : Finset V) (k : ℕ) (v : V) :
    (cutChoices G S k v).card=min k (neighborsIn G v Sᶜ).card :=
  (Classical.choose_spec (exists_subset_card_eq (min_le_right k (neighborsIn G v Sᶜ).card))).2

theorem cutChoices_not_mem (G : SimpleGraph V) (S : Finset V) (k : ℕ) {v w : V}
    (hw : w∈cutChoices G S k v) : w∉S :=
  mem_compl.mp (mem_filter.mp (cutChoices_subset G S k v hw)).1

def truncatedCut (G : SimpleGraph V) (S : Finset V) (k : ℕ) : SimpleGraph V where
  Adj v w := (v∈S ∧ w∈cutChoices G S k v) ∨ (w∈S ∧ v∈cutChoices G S k w)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h => by
    rcases h with h | h <;> exact (cutChoices_not_mem G S k h.2) h.1
    ⟩

theorem truncatedCut_le (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    truncatedCut G S k≤G := by
  intro v w h
  rcases h with h | h
  · exact (mem_filter.mp (cutChoices_subset G S k v h.2)).2
  · exact G.adj_symm (mem_filter.mp (cutChoices_subset G S k w h.2)).2

theorem truncatedCut_bipartite (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    (truncatedCut G S k).IsBipartiteWith (S:Set V) (↑(Sᶜ):Set V) where
  disjoint := by simp only [coe_compl]; exact disjoint_compl_right
  mem_of_adj := by
    intro v w h
    rcases h with h | h
    · exact Or.inl ⟨h.1,mem_compl.mpr (cutChoices_not_mem G S k h.2)⟩
    · exact Or.inr ⟨mem_compl.mpr (cutChoices_not_mem G S k h.2),h.1⟩

theorem truncatedCut_degree_left (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    {v : V} (hv : v∈S) :
    (truncatedCut G S k).degree v=min k (neighborsIn G v Sᶜ).card := by
  rw [← card_neighborFinset_eq_degree]
  have he : (truncatedCut G S k).neighborFinset v=cutChoices G S k v := by
    ext w
    rw [mem_neighborFinset]
    constructor
    · rintro (h | h)
      · exact h.2
      · exact False.elim ((cutChoices_not_mem G S k h.2) hv)
    · intro hw; exact Or.inl ⟨hv,hw⟩
  rw [he,cutChoices_card]

theorem truncatedCut_degree_right (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    {v : V} (hv : v∉S) : (truncatedCut G S k).degree v≤S.card := by
  rw [← card_neighborFinset_eq_degree]
  apply card_le_card
  intro w hw
  have he := ((truncatedCut G S k).mem_neighborFinset v w).mp hw
  rcases he with h | h
  · exact False.elim (hv h.1)
  · exact h.1

theorem truncatedCut_edge_count (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    (truncatedCut G S k).edgeSet.ncard=∑ v∈S, min k (neighborsIn G v Sᶜ).card := by
  have hh := (truncatedCut G S k).isBipartiteWith_sum_degrees_eq_card_edges
    (truncatedCut_bipartite G S k)
  have he : ∑ v∈S, (truncatedCut G S k).degree v=∑ v∈S, min k (neighborsIn G v Sᶜ).card := by
    exact sum_congr rfl (fun v hv => truncatedCut_degree_left G S k hv)
  simpa only [he,SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card'] using hh.symm

theorem truncatedCut_degree_bound (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (hk : S.card≤k) (v : V) : (truncatedCut G S k).degree v≤k := by
  by_cases hv : v∈S
  · rw [truncatedCut_degree_left G S k hv]; exact min_le_left _ _
  · exact (truncatedCut_degree_right G S k hv).trans hk

theorem truncatedCut_endpoint_sum (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    {v w : V} (h : (truncatedCut G S k).Adj v w) :
    (truncatedCut G S k).degree v+(truncatedCut G S k).degree w≤k+S.card := by
  have hb := (truncatedCut_bipartite G S k).mem_of_adj h
  rcases hb with hb | hb
  · rw [truncatedCut_degree_left G S k hb.1]
    exact Nat.add_le_add (min_le_left _ _) (truncatedCut_degree_right G S k (mem_compl.mp hb.2))
  · rw [truncatedCut_degree_left G S k hb.2]
    have hh := truncatedCut_degree_right G S k (mem_compl.mp hb.1)
    omega

end
end Cycle13
