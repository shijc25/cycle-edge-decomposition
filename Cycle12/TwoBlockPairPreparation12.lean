import Cycle12.BlockEdgePartition12
import Cycle12.Foundations.TwoSidedPairRemoval

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Preparation of a single crossing class. The two actual pairing
passes belong to different prescribed cores; the retained edges form a
matching and all removed original edges are explicitly accounted for. -/
theorem prepare_two_blocks (G : SimpleGraph V) (U T : Finset V)
    (hUT : Disjoint U T)
    (hcross : ∀ {x y},G.Adj x y → (x∈U ∧ y∈T) ∨ (x∈T ∧ y∈U)) :
    ∃ (P : CenterPairings G U) (Q : CenterPairings P.residue Uᶜ),
      (∀ e : P.Index,P.left e∈U ∧ P.right e∈U) ∧
      (∀ e : Q.Index,Q.left e∈T ∧ Q.right e∈T) ∧
      (∀ v,Q.residue.degree v ≤ 1) ∧
      Disjoint P.used Q.used ∧ Disjoint P.used Q.residue.edgeSet ∧
      Disjoint Q.used Q.residue.edgeSet ∧
      P.used∪Q.used∪Q.residue.edgeSet=G.edgeSet ∧
      Q.residue.edgeSet.ncard+2*(Fintype.card P.Index+Fintype.card Q.Index)=G.edgeSet.ncard := by
  have hbip : ∀ {x y},G.Adj x y → (x∈U ∧ y∉U) ∨ (x∉U ∧ y∈U) := by
    intro x y hxy
    rcases hcross hxy with h | h
    · exact Or.inl ⟨h.1,fun hy => Finset.disjoint_left.mp hUT hy h.2⟩
    · exact Or.inr ⟨fun hx => Finset.disjoint_left.mp hUT hx h.1,h.2⟩
  obtain ⟨P,Q,hdegree,hPQ,hPR,hQR,hcover,hcard⟩ := two_sided_pair_removal G U hbip
  have hT {x y : V} (hxy : P.residue.Adj x y) (hy : y∈Uᶜ) : y∈T := by
    rcases hcross hxy.1 with h | h
    · exact h.2
    · exact False.elim ((mem_compl.mp hy) h.2)
  refine ⟨P,Q,?_,?_,hdegree,hPQ,hPR,hQR,hcover,hcard⟩
  · intro e
    exact ⟨e.2.val.out.1.property.1,e.2.val.out.2.property.1⟩
  · intro e
    exact ⟨hT e.2.val.out.1.property.2 e.2.val.out.1.property.1,
      hT e.2.val.out.2.property.2 e.2.val.out.2.property.1⟩

/-- The outside class needs only the first pass: at most one retained
edge from each uncontracted vertex into this active block. -/
theorem prepare_block_outside (G : SimpleGraph V) (U T : Finset V)
    (hUT : Disjoint U T)
    (hcross : ∀ {x y},G.Adj x y → (x∈U ∧ y∈T) ∨ (x∈T ∧ y∈U)) :
    ∃ P : CenterPairings G U,
      (∀ v,v∉U → P.residue.degree v ≤ 1) ∧
      Disjoint P.used P.residue.edgeSet ∧ P.used∪P.residue.edgeSet=G.edgeSet ∧
      P.residue.edgeSet.ncard+2*Fintype.card P.Index=G.edgeSet.ncard := by
  obtain ⟨P⟩ := exists_centerPairings G U
  have hside : ∀ {z v},G.Adj z v → z∉U → v∈U := by
    intro z v hz hnot
    rcases hcross hz with h | h
    · exact False.elim (hnot h.1)
    · exact h.2
  refine ⟨P,fun v hv => P.residue_exterior_degree_le_one hside ⟨v,hv⟩,?_,?_,P.exact_edge_account⟩
  · rw [CenterPairings.residue,edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_right
  · rw [CenterPairings.residue,edgeSet_deleteEdges]
    exact Set.union_diff_cancel P.used_subset

end
end Cycle12
