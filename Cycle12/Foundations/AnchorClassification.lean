import Cycle12.Foundations.AnchorGeometry
import Cycle12.Foundations.OrientedSampleCut

namespace Cycle13
open Finset SimpleGraph Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem external_classified_side_lower (X S : Finset V) {miss : ℝ}
    (hmiss : ((X\S).card:ℝ) ≤ miss*X.card) :
    (1-miss)*X.card ≤ (S.card:ℝ) := by
  have hc : ((X\S).card:ℝ)+((X∩S).card:ℝ)=X.card := by
    exact_mod_cast card_sdiff_add_card_inter X S
  have hi : ((X∩S).card:ℝ) ≤ S.card := by exact_mod_cast card_le_card (inter_subset_right (s₁:=X) (s₂:=S))
  nlinarith

theorem classified_sample_complement_lower (G : SimpleGraph V) (U C S : Finset V)
    (hCU : C⊆U) (hsmall : 2*C.card ≤ U.card) {δ budget : ℝ} (hδ : 0 < δ)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (herr : sampledErrorWeight G U C (U∩S) ≤ budget) :
    (U.card:ℝ)/2-budget/δ ≤ ((U\S).card:ℝ) := by
  have hd := sampled_error_card_bound G U C (U∩S) hCU inter_subset_left hdeg
  have hdist : ((C ∆ (U∩S)).card:ℝ) ≤ budget/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hc := card_le_add_symmDiff (U∩S) C
  rw [symmDiff_comm (U∩S) C] at hc
  have hcR : ((U∩S).card:ℝ) ≤ C.card+(C ∆ (U∩S)).card := by exact_mod_cast hc
  have hpart : ((U\S).card:ℝ)+((U∩S).card:ℝ)=U.card := by
    exact_mod_cast card_sdiff_add_card_inter U S
  have hsmallR : 2*(C.card:ℝ) ≤ U.card := by exact_mod_cast hsmall
  linarith

theorem anchor_classified_complement_population (G : SimpleGraph V) (U X C S : Finset V)
    (hCU : C⊆U) (hsmall : 2*C.card ≤ U.card)
    {δ err L lower scale b popB : ℝ} (hδ : 0 < δ) (herr : 0 ≤ err)
    (hL : 0 ≤ L) (hscale : 0 < scale)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (herror : sampledErrorWeight G U C (U∩S) ≤ err*L*X.card)
    (hlower : lower ≤ (U.card:ℝ))
    (hpop : scale*popB+b ≤ lower/2-err*L*Fintype.card V/δ)
    (hupper : ((U\S).card:ℝ) ≤ scale*Sᶜ.card+b) : popB ≤ (Sᶜ.card:ℝ) := by
  have hs := classified_sample_complement_lower G U C S hCU hsmall hδ hdeg herror
  have hx : (X.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ X
  have he := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hx (mul_nonneg herr hL)) hδ.le
  apply (mul_le_mul_iff_right₀ hscale).mp
  linarith

theorem anchor_classified_population (G : SimpleGraph V) (U X C S : Finset V)
    (hXU : Disjoint X U) (hCU : C⊆U) (hsmall : 2*C.card ≤ U.card)
    {δ err L lower scale b popB miss c : ℝ} (hδ : 0 < δ) (herr : 0 ≤ err)
    (hL : 0 ≤ L) (hscale : 0 < scale) (hc : 0 ≤ c) (hca : c ≤ 1-miss)
    (hcb : c*((Fintype.card V:ℝ)-lower) ≤ popB)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (herror : sampledErrorWeight G U C (U∩S) ≤ err*L*X.card)
    (hmiss : ((X\S).card:ℝ) ≤ miss*X.card) (hlower : lower ≤ (U.card:ℝ))
    (hpop : scale*popB+b ≤ lower/2-err*L*Fintype.card V/δ)
    (hupper : ((U\S).card:ℝ) ≤ scale*Sᶜ.card+b) :
    c*X.card ≤ ((smallerCutSide S).card:ℝ) := by
  have ha := external_classified_side_lower X S hmiss
  have hb := anchor_classified_complement_population G U X C S hCU hsmall
    hδ herr hL hscale hdeg herror hlower hpop hupper
  have hxu : X.card+U.card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint hXU]
    exact card_le_univ _
  have hxuR : (X.card:ℝ)+U.card ≤ Fintype.card V := by exact_mod_cast hxu
  have hxb : (X.card:ℝ) ≤ (Fintype.card V:ℝ)-lower := by linarith
  apply smallerCutSide_population S
  · exact (mul_le_mul_of_nonneg_right hca (Nat.cast_nonneg _)).trans ha
  · exact ((mul_le_mul_of_nonneg_left hxb hc).trans hcb).trans hb

end
end Cycle13
