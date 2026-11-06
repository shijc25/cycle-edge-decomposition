import Cycle12.BiasedBankSplit

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Fair edge sampling gives two disjoint expanding banks, each retaining
511/1024 of every cut. This is the balanced completion branch. -/
theorem balanced_completion_banks (G : SimpleGraph V) {h : ℝ}
    (hn : 2 ≤ Fintype.card V) (hh : 0 < h)
    (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hscale : 4*log (Fintype.card V:ℝ)+8 ≤ h/524288) :
    ∃ H₁ H₂ : SimpleGraph V, H₁ ≤ G ∧ H₂ ≤ G ∧
      Disjoint H₁.edgeSet H₂.edgeSet ∧
      OAI.ErdosGallai.CutExpansion H₁ ((511/1024)*h) ∧
      OAI.ErdosGallai.CutExpansion H₂ ((511/1024)*h) := by
  let q : unitInterval := ⟨1/2,by norm_num⟩
  obtain ⟨hgap,hfail⟩ := sharp_cut_failure_quarter (ε:=1/1024) (h:=h) (by omega : 1 ≤ Fintype.card V)
    (by convert hscale using 1 <;> ring)
  obtain ⟨ω,htrue,hfalse⟩ := exists_direct_edge_split G q (ε:=1/1024)
    (f:=511/1024) (g:=511/1024) (budget:=1/4)
    (by norm_num) hh hn (cutExpansion_proper_cut hh.le hexp)
    (by norm_num [q]) (by norm_num [q]) hgap hfail (by norm_num)
  have hp := splitBank_partition G ω
  refine ⟨splitBank G ω true,splitBank G ω false,?_,?_,?_,?_,?_⟩
  · exact fun _ _ h => h.1
  · exact fun _ _ h => h.1
  · exact SimpleGraph.disjoint_edgeSet.mpr hp.1
  · exact cutExpansion_of_cut_retention (by norm_num) hexp htrue
  · exact cutExpansion_of_cut_retention (by norm_num) hexp hfalse

end
end Cycle12
