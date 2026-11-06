import Cycle12.Foundations.IndexedSupport

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem exists_vertex_away (H : SimpleGraph V) (S E : Finset V) {d : ℕ}
    (hd : ∀ v, H.degree v ≤ d)
    (hspace : E.card+S.card*(d+1) < Fintype.card V) :
    ∃ v, v∉E ∧ v∉S ∧ ∀ u∈S, ¬H.Adj v u := by
  let N : V → Finset V := fun u => insert u (H.neighborFinset u)
  let bad := E∪S.biUnion N
  have hN : ∀ u∈S, (N u).card ≤ d+1 := by
    intro u hu
    have hh := card_insert_le u (H.neighborFinset u)
    rw [card_neighborFinset_eq_degree] at hh
    have hu := hd u
    change (N u).card ≤ _ at hh
    omega
  have hbad : bad.card ≤ E.card+S.card*(d+1) := by
    calc
      _ ≤ E.card+(S.biUnion N).card := card_union_le _ _
      _ ≤ E.card+∑ u∈S, (N u).card := Nat.add_le_add_left card_biUnion_le _
      _ ≤ E.card+∑ _u∈S, (d+1) := Nat.add_le_add_left (sum_le_sum hN) _
      _ = _ := by simp
  obtain ⟨v,hv,hbadV⟩ := exists_mem_notMem_of_card_lt_card
    (show bad.card < (univ : Finset V).card by rw [card_univ]; omega)
  refine ⟨v,?_,?_,?_⟩
  · intro hvE
    exact hbadV (mem_union_left _ hvE)
  · intro hvS
    exact hbadV (mem_union_right _ (mem_biUnion.mpr ⟨v,hvS,mem_insert_self _ _⟩))
  · intro u hu hvu
    exact hbadV (mem_union_right _ (mem_biUnion.mpr ⟨u,hu,mem_insert_of_mem
      ((H.mem_neighborFinset u v).mpr hvu.symm)⟩))

theorem exists_independent_extension (H : SimpleGraph V) (S E : Finset V) {d k : ℕ}
    (hd : ∀ v, H.degree v ≤ d) (hS : H.IsIndepSet S) (hSE : Disjoint S E) (hSk : S.card ≤ k)
    (hspace : E.card+(k-1)*(d+1) < Fintype.card V) :
    ∃ B : Finset V, S⊆B ∧ B.card=k ∧ Disjoint B E ∧ H.IsIndepSet B := by
  let T := (univ : Finset (Finset V)).filter
    (fun B => S⊆B ∧ B.card ≤ k ∧ Disjoint B E ∧ H.IsIndepSet B)
  have hT : T.Nonempty := ⟨S,mem_filter.mpr ⟨mem_univ _,Subset.rfl,hSk,hSE,hS⟩⟩
  obtain ⟨B,hBT,hmax⟩ := exists_max_image T Finset.card hT
  have hB := (mem_filter.mp hBT).2
  refine ⟨B,hB.1,?_,hB.2.2.1,hB.2.2.2⟩
  by_contra hne
  have hsmall : B.card ≤ k-1 := by omega
  have hmul := Nat.mul_le_mul_right (d+1) hsmall
  obtain ⟨v,hvE,hvB,hno⟩ := exists_vertex_away H B E hd (by omega)
  have hnew : insert v B∈T := by
    refine mem_filter.mpr ⟨mem_univ _,hB.1.trans (subset_insert _ _),?_,?_,?_⟩
    · rw [card_insert_of_notMem hvB]; omega
    · exact Finset.disjoint_left.mpr (by
        intro u hu huE
        rcases mem_insert.mp hu with rfl | hu
        · exact hvE huE
        · exact Finset.disjoint_left.mp hB.2.2.1 hu huE)
    · intro x hx y hy hxy
      rcases mem_insert.mp hx with hx | hx <;> rcases mem_insert.mp hy with hy | hy
      · exact (hxy (hx.trans hy.symm)).elim
      · subst x; exact hno y hy
      · subst y; exact fun hyx => hno x hx hyx.symm
      · exact hB.2.2.2 hx hy hxy
  have hh := hmax (insert v B) hnew
  rw [card_insert_of_notMem hvB] at hh
  omega

end
end Cycle13
