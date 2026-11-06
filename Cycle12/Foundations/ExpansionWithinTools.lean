import Cycle12.Foundations.ExpansionPruning

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cutExpansion_of_small (G : SimpleGraph V) {h : ℝ}
    (hs : ∀ U : Finset V, 2*U.card ≤ Fintype.card V →
      h*U.card ≤ (cutSize G U:ℝ)) : OAI.ErdosGallai.CutExpansion G h := by
  intro U
  have hc : U.card+Uᶜ.card=Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ U)
  rw [← cutSize_eq_interedges]
  by_cases hu : 2*U.card ≤ Fintype.card V
  · have hh : (U.card:ℝ) ≤ Uᶜ.card := by exact_mod_cast (show U.card ≤ Uᶜ.card by omega)
    rw [min_eq_left hh]
    exact hs U hu
  · have hh : (Uᶜ.card:ℝ) ≤ U.card := by exact_mod_cast (show Uᶜ.card ≤ U.card by omega)
    rw [min_eq_right hh]
    simpa only [cutSize_compl] using hs Uᶜ (by omega)

theorem ExpansionWithin.mono {G : SimpleGraph V} {S : Finset V} {h h' : ℝ}
    (hexp : ExpansionWithin G S h) (hh : h' ≤ h) : ExpansionWithin G S h' := by
  intro U hU hsmall
  exact (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg _)).trans (hexp U hU hsmall)

/-- Removing X vertices loses at most |X| in the cut-expansion constant.
The retained graph is induced on the actual difference S minus X. -/
theorem ExpansionWithin.delete_vertices {G : SimpleGraph V} {S : Finset V} {h : ℝ}
    (hexp : ExpansionWithin G S h) (X : Finset V) :
    ExpansionWithin G (S\X) (h-X.card) := by
  intro U hU hsmall
  have hUS : U ⊆ S := hU.trans Finset.sdiff_subset
  have hsmallS : 2*U.card ≤ S.card :=
    hsmall.trans (Finset.card_le_card Finset.sdiff_subset)
  have hex := hexp U hUS hsmallS
  have hcover : G.interedges U (S\U) ⊆
      G.interedges U ((S\X)\U) ∪ (U ×ˢ X) := by
    intro e he
    obtain ⟨hu,hv,hadj⟩ := G.mem_interedges_iff.mp he
    by_cases hx : e.2 ∈ X
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hu,hx⟩)
    · apply Finset.mem_union_left
      exact G.mem_interedges_iff.mpr ⟨hu,
        Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1,hx⟩,
          (Finset.mem_sdiff.mp hv).2⟩,hadj⟩
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [Finset.card_product] at hc
  have hcR : ((G.interedges U (S\U)).card:ℝ) ≤
      (G.interedges U ((S\X)\U)).card+(U.card:ℝ)*X.card := by exact_mod_cast hc
  nlinarith only [hex,hcR]

theorem ExpansionWithin.induce {G : SimpleGraph V} {S : Finset V} {h : ℝ}
    (hexp : ExpansionWithin G S h) :
    OAI.ErdosGallai.CutExpansion (G.induce (S:Set V)) h := by
  let H := G.induce (S:Set V)
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  suffices hh : OAI.ErdosGallai.CutExpansion H h by
    convert hh using 1
  apply cutExpansion_of_small
  intro U hsmall
  let A := U.image Subtype.val
  have hA : A ⊆ S := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact x.property
  have hcard : A.card=U.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hS : Fintype.card (S:Set V)=S.card := Fintype.card_of_finset' S (fun _ => Iff.rfl)
  have hsmallA : 2*A.card ≤ S.card := by
    rw [hcard]
    simpa only [hS] using hsmall
  have hx := hexp A hA hsmallA
  rw [hcard] at hx
  change h*(U.card:ℝ) ≤ (cutSize (G.induce (S:Set V)) U:ℝ)
  rw [cutSize_induce]
  exact hx

end
end Cycle13
