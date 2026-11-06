import Cycle12.Foundations.DeletedComponentCuts
import Cycle12.Foundations.ExpansionWithinTools

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cutSize_sdiff_add (G F : SimpleGraph V) (hFG : F ≤ G) (S : Finset V) :
    cutSize (G\F) S+cutSize F S=cutSize G S := by
  have he : G.interedges S Sᶜ=(G\F).interedges S Sᶜ ∪ F.interedges S Sᶜ := by
    ext e
    simp only [mem_union,SimpleGraph.mem_interedges_iff,SimpleGraph.sdiff_adj]
    constructor
    · rintro ⟨ha,hb,hab⟩
      by_cases hf : F.Adj e.1 e.2
      · exact Or.inr ⟨ha,hb,hf⟩
      · exact Or.inl ⟨ha,hb,hab,hf⟩
    · rintro (⟨ha,hb,hab,hf⟩ | ⟨ha,hb,hf⟩)
      · exact ⟨ha,hb,hab⟩
      · exact ⟨ha,hb,hFG hf⟩
  have hd : Disjoint ((G\F).interedges S Sᶜ) (F.interedges S Sᶜ) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (((G\F).mem_interedges_iff.mp he).2.2).2 ((F.mem_interedges_iff.mp hf).2.2)
  simp only [cutSize_eq_interedges]
  rw [he,Finset.card_union_of_disjoint hd]
  congr 1
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_interedges_iff]

/-- A bounded-degree deletion loses at most that degree bound in expansion. -/
theorem cutExpansion_sdiff_degree_bound (G F : SimpleGraph V) {h : ℝ} {D : ℕ}
    (hFG : F ≤ G) (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hdeg : ∀ v, F.degree v ≤ D) : OAI.ErdosGallai.CutExpansion (G\F) (h-D) := by
  let H := G\F
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  suffices hx : OAI.ErdosGallai.CutExpansion H (h-D) by convert hx using 1
  apply cutExpansion_of_small
  intro S hS
  have hx := cutExpansion_small G hexp hS
  have hc := cutSize_sdiff_add G F hFG S
  have hb := cutSize_le_degree_cap F S hdeg
  have hcR : (cutSize (G\F) S:ℝ)+cutSize F S=cutSize G S := by exact_mod_cast hc
  have hbR : (cutSize F S:ℝ) ≤ (D:ℝ)*S.card := by exact_mod_cast hb
  nlinarith only [hx,hcR,hbR]

end
end Cycle13
