import Cycle12.Pruning

/-! Simple-graph expansion loses at most one unit per deleted vertex. -/
namespace Cycle12

universe u
variable {V : Type u} [Fintype V]
open scoped Classical

theorem cutExpandsOn_delete_vertices {G : SimpleGraph V} {U W : Finset V} {h : ℝ}
    (hG : CutExpandsOn G U h) (hWU : W ⊆ U) :
    CutExpandsOn G W (h-(U \ W).card) := by
  intro T hTW hTsmall
  have hTsmallU : 2*T.card ≤ U.card := hTsmall.trans (Finset.card_le_card hWU)
  have he := hG T (hTW.trans hWU) hTsmallU
  have hl : (cutCount G T (U \ T) : ℝ) ≤
      (cutCount G T (W \ T) : ℝ) + (T.card : ℝ)*(U \ W).card := by
    exact_mod_cast cutCount_delete_vertices G U W T
  nlinarith

theorem cutExpandsOn_mono_parameter {G : SimpleGraph V} {U : Finset V} {h k : ℝ}
    (hG : CutExpandsOn G U h) (hkh : k ≤ h) : CutExpandsOn G U k := by
  intro T hTU hTsmall
  exact (mul_le_mul_of_nonneg_right hkh (Nat.cast_nonneg T.card)).trans (hG T hTU hTsmall)

theorem cutExpandsOn_delete_budget {G : SimpleGraph V} {U W : Finset V} {h d : ℝ}
    (hG : CutExpandsOn G U h) (hWU : W ⊆ U) (hdel : ((U \ W).card : ℝ) ≤ d) :
    CutExpandsOn G W (h-d) :=
  cutExpandsOn_mono_parameter (cutExpandsOn_delete_vertices hG hWU) (by linarith)

end Cycle12
