import Cycle12.Foundations.BipartitePairRemoval

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The two consecutive center-pairing passes used before full block
contraction. The remainder has degree at most one at both ends, hence is
a matching. Every removed edge belongs to an actual two-edge path. -/
theorem two_sided_pair_removal (G : SimpleGraph V) (U : Finset V)
    (hbip : ∀ {x y},G.Adj x y → (x∈U ∧ y∉U) ∨ (x∉U ∧ y∈U)) :
    ∃ (P : CenterPairings G U) (Q : CenterPairings P.residue Uᶜ),
      (∀ v,Q.residue.degree v ≤ 1) ∧
      Disjoint P.used Q.used ∧
      Disjoint P.used Q.residue.edgeSet ∧
      Disjoint Q.used Q.residue.edgeSet ∧
      P.used∪Q.used∪Q.residue.edgeSet=G.edgeSet ∧
      Q.residue.edgeSet.ncard+2*(Fintype.card P.Index+Fintype.card Q.Index)=G.edgeSet.ncard := by
  obtain ⟨P⟩ := exists_centerPairings G U
  obtain ⟨Q⟩ := exists_centerPairings P.residue Uᶜ
  have hside : ∀ {z v},G.Adj z v → z∉U → v∈U := by
    intro z v hz hnot
    rcases hbip hz with h | h
    · exact False.elim (hnot h.1)
    · exact h.2
  have hside' : ∀ {z v},P.residue.Adj z v → z∉Uᶜ → v∈Uᶜ := by
    intro z v hz hnot
    have hzU : z∈U := by simpa only [Finset.mem_compl,not_not] using hnot
    rcases hbip hz.1 with h | h
    · exact Finset.mem_compl.mpr h.2
    · exact False.elim (h.1 hzU)
  have hQP : Q.residue ≤ P.residue := fun _ _ h => h.1
  have hR : Q.residue.edgeSet=P.residue.edgeSet\Q.used := SimpleGraph.edgeSet_deleteEdges _
  have hP : P.residue.edgeSet=G.edgeSet\P.used := SimpleGraph.edgeSet_deleteEdges _
  have hQused : Q.used ⊆ G.edgeSet\P.used := by rw [← hP]; exact Q.used_subset
  refine ⟨P,Q,?_,?_,?_,?_,?_,?_⟩
  · intro v
    by_cases hv : v∈U
    · exact Q.residue_exterior_degree_le_one hside' ⟨v,by simpa using hv⟩
    · exact (SimpleGraph.degree_le_of_le hQP (v:=v)).trans
        (P.residue_exterior_degree_le_one hside ⟨v,hv⟩)
  · exact Set.disjoint_left.mpr (fun _ he hf => (hQused hf).2 he)
  · rw [hR,hP]
    exact Set.disjoint_left.mpr (fun _ he hf => hf.1.2 he)
  · rw [hR]
    exact Set.disjoint_left.mpr (fun _ he hf => hf.2 he)
  · rw [hR,hP]
    ext e
    constructor
    · rintro ((he | he) | he)
      · exact P.used_subset he
      · exact (hQused he).1
      · exact he.1.1
    · intro he
      by_cases hPe : e∈P.used
      · exact Or.inl (Or.inl hPe)
      by_cases hQe : e∈Q.used
      · exact Or.inl (Or.inr hQe)
      · exact Or.inr ⟨⟨he,hPe⟩,hQe⟩
  · have hp := P.exact_edge_account
    have hq := Q.exact_edge_account
    omega

end
end Cycle13
