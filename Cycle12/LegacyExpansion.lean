import Cycle12.Pruning
import Cycle12.Foundations.ExpansionPruning

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem boundaryCount_eq_legacy_cutSize (G : SimpleGraph V) (S : Finset V) :
    boundaryCount G S=Cycle13.cutSize G S := by
  rw [boundaryCount,cutCount_eq_filter_card,Cycle13.cutSize]
  have heq : ((G.edgeFinset.filter (Crosses S Sᶜ)):Set (Sym2 V))=
      (Cycle13.cutGraph G S).edgeSet := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_coe,mem_filter,SimpleGraph.mem_edgeFinset,crosses_pair,
        SimpleGraph.mem_edgeSet,Cycle13.cutGraph,SimpleGraph.between_adj,
        mem_compl,Set.mem_compl_iff]
      tauto
  rw [← heq,Set.ncard_coe_finset]

theorem cutExpands_iff_legacy (G : SimpleGraph V) (h : ℝ) :
    CutExpands G h ↔ OAI.ErdosGallai.CutExpansion G h := by
  constructor
  · intro hexp S
    have hc := Finset.card_add_card_compl S
    by_cases hs : 2*S.card ≤ Fintype.card V
    · have hside : (S.card:ℝ) ≤ Sᶜ.card := by
        exact_mod_cast (show S.card ≤ Sᶜ.card by omega)
      have hb := hexp S hs
      simpa only [min_eq_left hside,boundaryCount_eq_legacy_cutSize,
        Cycle13.cutSize_eq_interedges] using hb
    · have hsmall : 2*Sᶜ.card ≤ Fintype.card V := by omega
      have hside : (Sᶜ.card:ℝ) ≤ S.card := by
        exact_mod_cast (show Sᶜ.card ≤ S.card by omega)
      have hb := hexp Sᶜ hsmall
      rw [boundaryCount_eq_legacy_cutSize,Cycle13.cutSize_compl,
        Cycle13.cutSize_eq_interedges] at hb
      simpa only [min_eq_right hside] using hb
  · intro hexp S hs
    simpa only [boundaryCount_eq_legacy_cutSize] using
      Cycle13.cutExpansion_small G hexp hs

end
end Cycle12
