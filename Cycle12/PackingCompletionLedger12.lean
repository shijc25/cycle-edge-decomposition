import Cycle12.PackingParity12
import Cycle12.ReserveGeometry12
import Cycle12.Foundations.PackingExtension

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Transfer a packing to any graph containing all its used edges. -/
def restrictPacking {G : SimpleGraph V} (P : CyclePacking G) (H : SimpleGraph V)
    (h : P.used ⊆ H.edgeSet) : CyclePacking H where
  count := P.count
  parts := P.parts
  cycles i := by
    obtain ⟨v,p,hp,he⟩ := P.cycles i
    have hs : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
      intro e he'
      exact h (Set.mem_iUnion.mpr ⟨i,he.symm ▸ he'⟩)
    exact ⟨v,p.transfer H hs,hp.transfer _,he.trans (Walk.edgeSet_transfer _ _).symm⟩
  disjoint := P.disjoint

theorem combine_residual_packings {G : SimpleGraph V} (P Q : CyclePacking G)
    (hQ : Q.used ⊆ P.residue.edgeSet) :
    ∃ T : CyclePacking G, T.count = P.count+Q.count ∧ T.used = P.used ∪ Q.used := by
  let S := restrictPacking Q P.residue hQ
  refine ⟨P.extend S,?_,?_⟩
  · exact CyclePacking.extend_count P S
  · exact CyclePacking.extend_used P S

/-- Parity eliminates the last possible outside spoke: an even residual
graph cannot have a positive degree bounded by one. -/
theorem even_graph_supported (G H R : SimpleGraph V) (U : Finset V)
    (hcover : H.edgeSet ⊆ R.edgeSet ∪ (insideGraph G U).edgeSet)
    (hR : ∀ v, v ∉ U → R.degree v ≤ 1) (heven : ∀ v, Even (H.degree v)) :
    ∀ x y, H.Adj x y → x ∈ U ∧ y ∈ U := by
  have hzero : ∀ v, v ∉ U → H.degree v = 0 := by
    intro v hv
    have hs : H.neighborFinset v ⊆ R.neighborFinset v := by
      intro w hw
      have hH := (H.mem_neighborFinset v w).mp hw
      rcases hcover (show s(v,w) ∈ H.edgeSet from hH) with h | h
      · exact (R.mem_neighborFinset v w).mpr h
      · exact (hv h.2.1).elim
    have hb := (card_le_card hs).trans (show (R.neighborFinset v).card ≤ 1 by
      rw [card_neighborFinset_eq_degree]; exact hR v hv)
    rw [card_neighborFinset_eq_degree] at hb
    have hp := heven v
    rw [Nat.even_iff] at hp
    omega
  have hin : ∀ x y, H.Adj x y → x ∈ U := by
    intro x y hxy
    by_contra hx
    have hp : 0 < (H.neighborFinset x).card := card_pos.mpr ⟨y,(H.mem_neighborFinset x y).mpr hxy⟩
    rw [card_neighborFinset_eq_degree,hzero x hx] at hp
    omega
  exact fun x y hxy => ⟨hin x y hxy,hin y x hxy.symm⟩

/-- Coverage of the bipartite remainder leaves only reserved or internal
edges after both passes. This is an exact statement about actual packings. -/
theorem two_pass_residue_edges {G R : SimpleGraph V} (U : Finset V)
    (P Q T : CyclePacking G) (hT : T.used = P.used ∪ Q.used)
    (hQ : (P.residue.deleteEdges (R.edgeSet ∪ (insideGraph G U).edgeSet)).edgeSet ⊆ Q.used) :
    T.residue.edgeSet ⊆ R.edgeSet ∪ (insideGraph G U).edgeSet := by
  intro e he
  rw [CyclePacking.residue,edgeSet_deleteEdges,hT] at he
  by_contra hrest
  apply he.2
  apply Or.inr
  apply hQ
  rw [edgeSet_deleteEdges,CyclePacking.residue,edgeSet_deleteEdges]
  exact ⟨⟨he.1,fun hp => he.2 (Or.inl hp)⟩,hrest⟩

end
end Cycle12
