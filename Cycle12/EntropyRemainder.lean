import Cycle12.EntropyExtraction

namespace Cycle12
open Real SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable

theorem entropy_potential_linear {h n L : ℝ} (hh : 0<h) (hn : 0≤n)
    (hnL : n≤L) (hhL : h≤L) :
    2*entropyPotential h n ≤ h*(1+log (L/h)/log 2)*n := by
  have hL : 0<L := hh.trans_le hhL
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hl : 0≤log (L/h)/log 2 := div_nonneg
    (log_nonneg ((one_le_div hh).mpr hhL)) hl2.le
  by_cases hsmall : n≤h
  · rw [entropy_potential_small hh hsmall]
    have hmul := mul_le_mul_of_nonneg_right hsmall hn
    have hmore : 0 ≤ h*(log (L/h)/log 2)*n := by positivity
    nlinarith only [hmul,hmore]
  · have hhn : h≤n := le_of_not_ge hsmall
    have hnpos : 0<n := hh.trans_le hhn
    rw [entropy_potential_large hh hhn]
    have hlo := log_le_log (div_pos hnpos hh) (div_le_div_of_nonneg_right hnL hh.le)
    have hd := div_le_div_of_nonneg_right hlo hl2.le
    have hm := mul_le_mul_of_nonneg_left (add_le_add_left hd 1) (mul_nonneg hh.le hn)
    nlinarith only [hm]

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Sparse-cut extraction with a bound in the ambient box order, including
small boxes; the residual graph and exact edge partition are retained. -/
theorem entropy_cut_extraction_bounded (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) {h L : ℝ} (hh : 1≤h) (hhL : h≤L)
    (hA : (A.card:ℝ)≤L) :
    ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V),
      (∀ P ∈ R, P.vertices ⊆ A ∧ h < (P.vertices.card:ℝ) ∧
        (P.vertices.card:ℝ)≤L ∧ CutExpansionOn P.graph P.vertices h) ∧
      R.Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      GraphPartition G (H :: R.map AssignedPiece.graph) ∧
      SupportedOn H A ∧
      2*(edgeCount H:ℝ) ≤ h*(1+log (L/h)/log 2)*A.card := by
  obtain ⟨R,H,hR,hd,hp,hs,hcost⟩ := entropy_cut_extraction G A hG h hh
  refine ⟨R,H,?_,hd,hp,hs,?_⟩
  · intro P hP
    obtain ⟨hPA,hPh,_,hPe⟩ := hR P hP
    have hcard : (P.vertices.card:ℝ)≤A.card := by exact_mod_cast Finset.card_le_card hPA
    exact ⟨hPA,hPh,hcard.trans hA,hPe⟩
  · have hb := entropy_potential_linear (by linarith : 0<h) (Nat.cast_nonneg (α:=ℝ) A.card) hA hhL
    linarith only [hcost,hb]

end
end Cycle12
