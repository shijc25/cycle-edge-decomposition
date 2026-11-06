import Cycle12.FixedStrongMajorityTransfer
import Cycle12.Foundations.OrientedSampleCut

namespace Cycle12
open Finset SimpleGraph Cycle13
open OAI.ErdosGallai.Sampling
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem joint_error_fraction_bounds {dm beta tau : ℝ}
    (hb : 0 < beta) (hbt : beta < tau) (hbd : beta < dm) :
    0 ≤ (tau-beta)/(tau+(dm-beta)/2) ∧ (tau-beta)/(tau+(dm-beta)/2) < 1 := by
  have hd : 0 < tau+(dm-beta)/2 := by linarith
  exact ⟨div_nonneg (sub_pos.mpr hbt).le hd.le,(div_lt_one hd).mpr (by linarith)⟩

theorem card_error_min_lower (U A B : Finset V) (hBU : B⊆U)
    (hsmall : 2*A.card ≤ U.card) {c : ℝ} (herr : ((A ∆ B).card:ℝ) ≤ c*A.card) :
    (1-c)*A.card ≤ min (B.card:ℝ) (U\B).card := by
  have h₁ : (A.card:ℝ) ≤ B.card+(A ∆ B).card := by exact_mod_cast card_le_add_symmDiff A B
  have h₂ : (B.card:ℝ) ≤ A.card+(A ∆ B).card := by
    simpa only [symmDiff_comm B A] using
      (show (B.card:ℝ) ≤ A.card+(B ∆ A).card by exact_mod_cast card_le_add_symmDiff B A)
  have hs : 2*(A.card:ℝ) ≤ U.card := by exact_mod_cast hsmall
  have hc : ((U\B).card:ℝ)=(U.card:ℝ)-B.card := by
    rw [card_sdiff_of_subset hBU,Nat.cast_sub (card_le_card hBU)]
  apply le_min
  · nlinarith only [herr,h₁]
  · rw [hc]
    nlinarith only [herr,h₂,hs]

theorem oriented_sample_card_upper (U S : Finset V) {scale err : ℝ}
    (h₁ : ((U∩S).card:ℝ) ≤ scale*S.card+err)
    (h₂ : ((U\S).card:ℝ) ≤ scale*Sᶜ.card+err) :
    min ((U∩S).card:ℝ) (U\S).card ≤ scale*(smallerCutSide S).card+err := by
  unfold smallerCutSide
  split_ifs
  · exact (min_le_left _ _).trans h₁
  · exact (min_le_right _ _).trans h₂

def fixedMajoritySmallSide (T A : Finset V) (xi : V → Finset V) : Finset V :=
  smallerCutSide (fixedMajoritySide univ T A xi)

/-- The improved population threshold uses both the new cut's minimum
degree bound and the original stable cut's size, without losing their
shared error fraction. -/
theorem strong_majority_oriented_witness (G : SimpleGraph V) (U T : Finset V)
    (xi : V → Finset V) {t : ℕ} {z dm beta tau q scale err : ℝ}
    (hz : 0 < z) (hb : 0 < beta) (hbt : beta < tau) (hbd : beta < dm) (hscale : 0 < scale)
    (hw : FixedGlobalStrongMajorityWitness G univ U T xi t z dm beta tau q)
    (hgood : ∀ A⊆T,
      ((U∩fixedMajoritySide univ T A xi).card:ℝ) ≤ scale*(fixedMajoritySide univ T A xi).card+err ∧
      ((U\fixedMajoritySide univ T A xi).card:ℝ) ≤ scale*(fixedMajoritySide univ T A xi)ᶜ.card+err) :
    ∃ A⊆T,
      (max (dm-tau) ((1-(tau-beta)/(tau+(dm-beta)/2))*(dm-beta))*z-err)/scale ≤
        ((fixedMajoritySmallSide T A xi).card:ℝ) ∧
      ((G.interedges (U∩fixedMajoritySmallSide T A xi) (U\fixedMajoritySmallSide T A xi)).card:ℝ) ≤
        tau*z*(scale*(fixedMajoritySmallSide T A xi).card+err) ∧
      (A.card:ℝ) ≤ (Real.exp 1-1)*((t:ℝ)/U.card)*
        ((scale*(fixedMajoritySmallSide T A xi).card+err)/(1-(tau-beta)/(tau+(dm-beta)/2)))+q := by
  obtain ⟨A,hAU,hAn,hsmall,ha,_,_,hcut,hsize,herr,hlabel⟩ := hw
  let C := fixedMajoritySide univ T (A∩T) xi
  let B := U∩C
  let c : ℝ := (tau-beta)/(tau+(dm-beta)/2)
  have hcomp : U\B=U\C := by ext v; simp [B]
  have hB : B⊆U := inter_subset_left
  change ((G.interedges B (U\B)).card:ℝ) < tau*z*min (B.card:ℝ) (U\B).card at hcut
  change (dm-tau)*z < min (B.card:ℝ) (U\B).card at hsize
  change ((A ∆ B).card:ℝ) ≤ c*A.card at herr
  have hc : c < 1 := (joint_error_fraction_bounds hb hbt hbd).2
  have hlow := card_error_min_lower U A B hB hsmall herr
  have hstrong := (mul_lt_mul_of_pos_left ha (sub_pos.mpr hc)).trans_le hlow
  have hu := hgood (A∩T) inter_subset_right
  have hupper := oriented_sample_card_upper U C hu.1 hu.2
  change min (B.card:ℝ) (U\C).card ≤ scale*(smallerCutSide C).card+err at hupper
  rw [← hcomp] at hupper
  have hmax : max (dm-tau) ((1-c)*(dm-beta))*z ≤ min (B.card:ℝ) (U\B).card := by
    rw [max_mul_of_nonneg _ _ hz.le]
    apply max_le hsize.le
    nlinarith only [hstrong]
  refine ⟨A∩T,inter_subset_right,?_,?_,?_⟩
  · apply (div_le_iff₀ hscale).mpr
    change max (dm-tau) ((1-c)*(dm-beta))*z-err ≤ (smallerCutSide C).card*scale
    nlinarith only [hmax,hupper]
  · change ((G.interedges (U∩smallerCutSide C) (U\smallerCutSide C)).card:ℝ) ≤ _
    rw [smallerCutSide_sample_cut]
    have hcut' : ((G.interedges (U∩C) (U\C)).card:ℝ) < tau*z*min (B.card:ℝ) (U\B).card := by
      simpa only [hcomp] using hcut
    exact hcut'.le.trans (mul_le_mul_of_nonneg_left hupper (mul_pos (hb.trans hbt) hz).le)
  · have haUpper : (A.card:ℝ) ≤ (scale*(smallerCutSide C).card+err)/(1-c) := by
      apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
      nlinarith only [hlow,hupper]
    have he : 0 ≤ (Real.exp 1-1)*((t:ℝ)/U.card) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
      · positivity
    have hm := mul_le_mul_of_nonneg_left haUpper he
    have hlabel' : ((A∩T).card:ℝ) ≤ (Real.exp 1-1)*((t:ℝ)/U.card)*A.card+q := by
      simpa only [inter_comm T A] using hlabel
    exact hlabel'.trans (add_le_add hm le_rfl)

end
end Cycle12
