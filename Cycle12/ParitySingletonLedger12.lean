import Cycle12.ParityThreeReservoir12
import Cycle12.InducedPackingLift12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Every residual edge outside the reservoirs is charged to an odd
outside vertex of degree one, so no vertex is charged twice. -/
theorem parity_outside_singleton_count (G H : SimpleGraph V) (U : Finset V)
    (hd : ∀ v,v∉U → H.degree v=if Even (G.degree v) then 0 else 1) :
    (H.deleteEdges (insideGraph H U).edgeSet).edgeSet.ncard≤
      (univ.filter (fun v => v∉U ∧ ¬Even (G.degree v))).card := by
  let T := univ.filter (fun v => v∉U ∧ ¬Even (G.degree v))
  let E := H.deleteEdges (insideGraph H U).edgeSet
  have hout {x y : V} (hxy : H.Adj x y) (hx : x∉U) : x∈T := by
    have hp := hxy.degree_pos_left
    have hh := hd x hx
    have hn : ¬Even (G.degree x) := by
      intro he
      rw [ite_eq_left he] at hh
      omega
    exact mem_filter.mpr ⟨mem_univ _,hx,hn⟩
  have hcover : E.edgeFinset⊆T.biUnion (fun v => H.incidenceFinset v) := by
    intro e he
    have he' := E.mem_edgeFinset.mp he
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hxy,hnot⟩ := deleteEdges_adj.mp he'
      by_cases hx : x∈U
      · have hy : y∉U := fun hy => hnot ⟨hxy,hx,hy⟩
        exact mem_biUnion.mpr ⟨y,hout hxy.symm hy,
          H.mem_incidenceFinset.mpr (H.mk'_mem_incidenceSet_right_iff.mpr hxy)⟩
      · exact mem_biUnion.mpr ⟨x,hout hxy hx,
          H.mem_incidenceFinset.mpr (H.mk'_mem_incidenceSet_left_iff.mpr hxy)⟩
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have he : E.edgeFinset.card=E.edgeSet.ncard := by
    rw [edgeFinset,Set.ncard_eq_toFinset_card']
  rw [he] at hcard
  change E.edgeSet.ncard≤T.card
  calc
    E.edgeSet.ncard≤∑ v∈T,(H.incidenceFinset v).card := hcard
    _ = ∑ _v∈T,(1:ℕ) := by
      apply Finset.sum_congr rfl
      intro v hv
      have hh := (mem_filter.mp hv).2
      rw [card_incidenceFinset_eq_degree,hd v hh.1,ite_eq_right hh.2]
    _ = T.card := by simp

theorem parity_outside_singletons_le_odd (G H : SimpleGraph V) (U : Finset V)
    (hd : ∀ v,v∉U → H.degree v=if Even (G.degree v) then 0 else 1) :
    (H.deleteEdges (insideGraph H U).edgeSet).edgeSet.ncard≤
      (univ.filter (fun v => ¬Even (G.degree v))).card := by
  apply (parity_outside_singleton_count G H U hd).trans
  apply Finset.card_le_card
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.2⟩

end
end Cycle12
