import Cycle12.FixedAnchorWitness
import Cycle12.MajorityPopulation
import Cycle12.Foundations.AnchorClassification

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem card_error_min_additive (U A B : Finset V) (hBU : B⊆U)
    (hsmall : 2*A.card ≤ U.card) {err : ℝ} (herr : ((A ∆ B).card:ℝ) ≤ err) :
    (A.card:ℝ)-err ≤ min (B.card:ℝ) (U\B).card := by
  have h₁ : (A.card:ℝ) ≤ B.card+(A ∆ B).card := by exact_mod_cast card_le_add_symmDiff A B
  have h₂ : (B.card:ℝ) ≤ A.card+(A ∆ B).card := by
    simpa only [symmDiff_comm B A] using
      (show (B.card:ℝ) ≤ A.card+(B ∆ A).card by exact_mod_cast card_le_add_symmDiff B A)
  have hs : 2*(A.card:ℝ) ≤ U.card := by exact_mod_cast hsmall
  have hc : ((U\B).card:ℝ)=(U.card:ℝ)-B.card := by
    rw [card_sdiff_of_subset hBU,Nat.cast_sub (card_le_card hBU)]
  apply le_min
  · linarith only [herr,h₁]
  · rw [hc]
    linarith only [herr,h₂,hs]

/-- External missed vertices and the classified complement jointly cap
the number of outside sources. This supplies the sharper population term
min(1-pLower,(1-raw)/(1-miss)). -/
theorem outside_anchor_population_cap (U X S : Finset V) (hdisj : Disjoint X U)
    {miss raw pLower : ℝ} (hmiss1 : miss < 1)
    (hmiss : ((X\S).card:ℝ) ≤ miss*X.card)
    (hcomp : raw*Fintype.card V ≤ (Sᶜ.card:ℝ))
    (hN : pLower*Fintype.card V ≤ (U.card:ℝ)) :
    (X.card:ℝ) ≤ min (1-pLower) ((1-raw)/(1-miss))*Fintype.card V := by
  have hx : (X.card:ℝ)+U.card ≤ Fintype.card V := by
    exact_mod_cast (show X.card+U.card ≤ Fintype.card V by
      rw [← card_union_of_disjoint hdisj]; exact card_le_univ _)
  have hpart : (S.card:ℝ)+Sᶜ.card=Fintype.card V := by
    exact_mod_cast card_add_card_compl S
  have hs := external_classified_side_lower X S hmiss
  have ha : (X.card:ℝ) ≤ (1-pLower)*Fintype.card V := by nlinarith only [hx,hN]
  have hb : (X.card:ℝ) ≤ ((1-raw)/(1-miss))*Fintype.card V := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sub_pos.mpr hmiss1)).mpr
    nlinarith only [hs,hcomp,hpart]
  by_cases hh : 1-pLower ≤ (1-raw)/(1-miss)
  · simpa only [min_eq_left hh] using ha
  · simpa only [min_eq_right (le_of_not_ge hh)] using hb

theorem anchor_oriented_sharp_population (G : SimpleGraph V) (U X C S : Finset V)
    {delta beta L ew miss scale intercept raw pLower ce : ℝ}
    (hd : 0 < delta) (hb : 0 < beta) (hL : 0 < L) (hew : 0 ≤ ew)
    (hmiss1 : miss < 1) (hscale : 0 < scale) (hce : 0 < ce)
    (hceFirst : ce ≤ 1-miss)
    (hceSecond : ce*min (1-pLower) ((1-raw)/(1-miss)) ≤ raw)
    (hN : pLower*Fintype.card V ≤ (U.card:ℝ))
    (hpop : scale*(raw*Fintype.card V)+intercept ≤
      (U.card:ℝ)/2-(ew+2)*L*Fintype.card V/delta)
    (hdeg : ∀ v, delta ≤ ((neighborsIn G v U).card:ℝ))
    (hexp : SampleCutExpansion G U beta) (hbad : BadAnchorCut G U X C L)
    (herror : jointCutError G U C (U∩S) ≤ ew*L*X.card)
    (hmiss : ((X\S).card:ℝ) ≤ miss*X.card)
    (hupper : ((U∩S).card:ℝ) ≤ scale*S.card+intercept ∧
      ((U\S).card:ℝ) ≤ scale*Sᶜ.card+intercept) :
    ce*X.card ≤ ((smallerCutSide S).card:ℝ) ∧
    max (min ((1-miss)*(beta*(delta-L)/L)) (raw*Fintype.card V))
      ((delta-L-intercept)/(scale+(ew+2)*L/(delta*ce))) ≤ ((smallerCutSide S).card:ℝ) ∧
    ((G.interedges (U∩smallerCutSide S) (U\smallerCutSide S)).card:ℝ) ≤ (1+ew)*L*X.card := by
  have hgeo := anchor_joint_error_geometry G U X C (U∩S) inter_subset_left hbad herror
  have hew : 0 ≤ ew+2 := by linarith
  have hcomp := anchor_classified_complement_population G U X C S hbad.2.1 hbad.2.2.1
    hd hew hL.le hscale (fun v _ => hdeg v) hgeo.1 le_rfl hpop hupper.2
  have hcap := outside_anchor_population_cap U X S hbad.1 hmiss1 hmiss hcomp hN
  have hs := external_classified_side_lower X S hmiss
  have hcepop : ce*X.card ≤ ((smallerCutSide S).card:ℝ) := by
    apply smallerCutSide_population
    · exact (mul_le_mul_of_nonneg_right hceFirst (Nat.cast_nonneg _)).trans hs
    · have h₁ := mul_le_mul_of_nonneg_left hcap hce.le
      have h₂ := mul_le_mul_of_nonneg_right hceSecond (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
      nlinarith only [h₁,h₂,hcomp]
  have hsizes := bad_anchor_cut_sizes G U X C hb hL (fun v _ => hdeg v) hexp hbad
  have hfirst : min ((1-miss)*(beta*(delta-L)/L)) (raw*Fintype.card V) ≤
      ((smallerCutSide S).card:ℝ) := by
    apply smallerCutSide_population
    · exact (min_le_left _ _).trans
        ((mul_le_mul_of_nonneg_left hsizes.2.2 (sub_nonneg.mpr hmiss1.le)).trans hs)
    · exact (min_le_right _ _).trans hcomp
  have hdist : ((C ∆ (U∩S)).card:ℝ) ≤ (ew+2)*L*X.card/delta := by
    have hh := sampled_error_card_bound G U C (U∩S) hbad.2.1 inter_subset_left (fun v _ => hdeg v)
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hh,hgeo.1]
  have hmin := card_error_min_additive U C (U∩S) inter_subset_left hbad.2.2.1 hdist
  have heq : U\(U∩S)=U\S := by ext v; simp
  rw [heq] at hmin
  have hcount := oriented_sample_card_upper U S hupper.1 hupper.2
  have hxUpper : (X.card:ℝ) ≤ ((smallerCutSide S).card:ℝ)/ce := by
    apply (le_div_iff₀ hce).mpr
    nlinarith only [hcepop]
  have herrUpper := mul_le_mul_of_nonneg_left hxUpper
    (div_nonneg (mul_nonneg hew hL.le) hd.le)
  have hden : 0 < scale+(ew+2)*L/(delta*ce) :=
    add_pos_of_pos_of_nonneg hscale (div_nonneg (mul_nonneg hew hL.le) (mul_pos hd hce).le)
  have hsecond : (delta-L-intercept)/(scale+(ew+2)*L/(delta*ce)) ≤
      ((smallerCutSide S).card:ℝ) := by
    apply (div_le_iff₀ hden).mpr
    simp only [div_eq_mul_inv,mul_inv_rev] at hmin herrUpper ⊢
    nlinarith only [hmin,hcount,hsizes.2.1,herrUpper]
  refine ⟨hcepop,max_le hfirst hsecond,?_⟩
  rw [smallerCutSide_sample_cut]
  have hh := hgeo.2
  rwa [heq] at hh

end
end Cycle12
