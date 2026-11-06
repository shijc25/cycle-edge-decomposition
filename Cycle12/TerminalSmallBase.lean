import Cycle12.Foundations.PackingOperations
import Cycle12.Foundations.PackingEraseCycle

namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem indexed_packing_edge_mass (G : SimpleGraph V) (P : Cycle13.CyclePacking G) :
    P.singles+∑ i, (P.parts i).ncard=G.edgeSet.ncard := by
  have hh := Set.ncard_sdiff_add_ncard_of_subset P.used_subset (Set.toFinite _)
  rw [Cycle13.CyclePacking.used,ncard_iUnion_disjoint _ P.disjoint] at hh
  simpa only [Cycle13.CyclePacking.singles,Cycle13.CyclePacking.residue,
    SimpleGraph.edgeSet_deleteEdges,Cycle13.CyclePacking.used] using hh

theorem indexed_packing_three_count_bound (G : SimpleGraph V)
    (P : Cycle13.CyclePacking G) : 3*P.count+P.singles ≤ G.edgeSet.ncard := by
  have hpart : ∀ i, 3 ≤ (P.parts i).ncard := by
    intro i
    obtain ⟨v,p,hp,he⟩ := P.cycles i
    rw [he,cycle_edgeSet_ncard hp]
    exact hp.three_le_length
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin P.count))) => hpart i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  have he := indexed_packing_edge_mass G P
  omega

theorem terminal_affine_forest (G : SimpleGraph V) (hforest : G.IsAcyclic) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-Cycle13.componentCount G)+6*G.edgeSet.ncard := by
  have he := Cycle13.forest_edges_add_components G hforest
  rw [SimpleGraph.edgeFinset_card,Set.fintypeCard_eq_ncard] at he
  refine ⟨Cycle13.CyclePacking.empty G,?_⟩
  simp only [Cycle13.CyclePacking.cost,Cycle13.CyclePacking.empty,
    Cycle13.CyclePacking.singles,Cycle13.CyclePacking.residue,Cycle13.CyclePacking.used,
    Set.iUnion_of_empty,SimpleGraph.deleteEdges_empty,Nat.mul_zero,Nat.zero_add]
  omega

/-- Every graph on one, two, or three vertices satisfies the terminal
affine bound, independently of the circumference classification. -/
theorem terminal_affine_card_le_three [Nonempty V] (G : SimpleGraph V)
    (horder : Fintype.card V ≤ 3) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  obtain ⟨P,hmin⟩ := Cycle13.CyclePacking.exists_minimum G
  have hs := P.minimum_singletons_le_rank hmin
  have hc : 0 < Cycle13.componentCount G := by
    unfold Cycle13.componentCount
    exact Nat.card_pos
  have hp := indexed_packing_three_count_bound G P
  have hm := G.card_edgeFinset_le_card_choose_two
  rw [SimpleGraph.edgeFinset_card,Set.fintypeCard_eq_ncard] at hm
  have hn := Fintype.card_pos (α:=V)
  refine ⟨P,?_⟩
  unfold Cycle13.CyclePacking.cost
  have hncase : Fintype.card V=1 ∨ Fintype.card V=2 ∨ Fintype.card V=3 := by omega
  rcases hncase with hh | hh | hh <;> norm_num only [hh,Nat.choose] at hm ⊢ <;> omega

end
end Cycle12
