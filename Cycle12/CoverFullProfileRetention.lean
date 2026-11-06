import Cycle12.CoverIrreducibleCuts
import Cycle12.RoundedProfileRetention

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section

/-- At zero light proportion the profile coefficient is multiplied by
zero. No artificial value or continuity assumption at that endpoint is needed. -/
theorem profile_finite_positive_interval_bound {I : Type} [Fintype I]
    (lo hi lower : I → ℝ) (alpha : ℝ → ℝ) {nu nuLower R lambda kappa : ℝ}
    (hn : 0 < nuLower) (hnu : nuLower ≤ nu) (hlambda : 1 ≤ lambda)
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ i, lo i ≤ t ∧ t ≤ hi i)
    (hprofile : ∀ i t, 0 < t → t ≤ 1 → lo i ≤ t → t ≤ hi i → lower i ≤ alpha (t*nu/R))
    (hcheck : ∀ i, kappa ≤ profileQuadratic nuLower lambda (lower i)
      (profileIntervalMinimizer nuLower lambda (lower i) (lo i) (hi i)))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    kappa ≤ nu*(1-t)*(lambda-t)+t*alpha (t*nu/R) := by
  obtain ⟨i,hi0,hi1⟩ := hcover t ht0 ht1
  have hb := (hcheck i).trans (profile_interval_minimum hn hi0 hi1)
  by_cases ht : 0 < t
  · exact hb.trans (profile_quadratic_lower hnu hlambda ht0 ht1 (hprofile i t ht ht1 hi0 hi1))
  · have hz : t=0 := le_antisymm (le_of_not_gt ht) ht0
    rw [hz] at hb ⊢
    simp only [profileQuadratic,sub_zero,mul_one,mul_zero,zero_mul,zero_div,add_zero] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_right hnu (by linarith only [hlambda]))

attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]

theorem truncated_cut_positive_profile_table (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (alpha : ℝ → ℝ) (lo hi lower : I → ℝ) {h N lambda nuLower kappa : ℝ}
    (hh : 0 < h) (hN : 0 < N) (hS : S.Nonempty) (hlambda : 1 ≤ lambda)
    (hn : 0 < nuLower) (hnu : nuLower ≤ S.card/h) (hcap : lambda*S.card ≤ (k:ℝ))
    (hprofile : ∀ X⊆S, alpha ((X.card:ℝ)/N)*h*X.card ≤ (cutSize G X:ℝ))
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ i, lo i ≤ t ∧ t ≤ hi i)
    (hlower : ∀ i t, 0 < t → t ≤ 1 → lo i ≤ t → t ≤ hi i →
      lower i ≤ alpha (t*(S.card/h)/(N/h)))
    (hcheck : ∀ i, kappa ≤ profileQuadratic nuLower lambda (lower i)
      (profileIntervalMinimizer nuLower lambda (lower i) (lo i) (hi i))) :
    kappa*h*S.card ≤ ((truncatedCut G S k).edgeSet.ncard:ℝ) := by
  obtain ⟨t,ht0,ht1,ht⟩ := truncated_cut_full_profile_scaled G S k alpha hh hN hS hcap hprofile
  have hbound := profile_finite_positive_interval_bound lo hi lower alpha hn hnu hlambda
    hcover hlower hcheck ht0 ht1
  have hs : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hb := (le_div_iff₀ (mul_pos hh hs)).mp (hbound.trans ht)
  nlinarith only [hb]

theorem cover_irreducible_exact_strength (G : SimpleGraph V)
    (hn : (0:ℝ) < Fintype.card V) (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hx : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ 17/250)
    (hI : CoverSparseCutIrreducible G) (S : Finset V) (hhalf : 2*(S.card:ℝ) ≤ Fintype.card V) :
    coverCutStrength (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet)) ((S.card:ℝ)/Fintype.card V)*
      coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*S.card ≤ cutSize G S := by
  by_cases hzero : S.card=0
  · rw [hzero,Nat.cast_zero,mul_zero]
    positivity
  have hspos : (0:ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hc := hI S (card_pos.mp (Nat.pos_of_ne_zero hzero)) hhalf
  rw [cover_cut_threshold_eq_strength hn hm hx (div_pos hspos hn)] at hc
  have hid : coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*(Fintype.card V:ℝ)*
      ((S.card:ℝ)/Fintype.card V)=coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*S.card := by field_simp
  rw [hid] at hc
  simpa only [mul_comm,mul_left_comm,mul_assoc] using hc

theorem cover_rational_full_profile_retained (G : SimpleGraph V) (S : Finset V)
    (C : Fin 16 → RatCutProfile) (hC : ∀ i, (C i).Valid)
    {ymax nu lambda kappa : ℝ}
    (hn : (0:ℝ) < Fintype.card V) (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hx : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ 17/250)
    (hI : CoverSparseCutIrreducible G)
    (hxl : ∀ i, ((C i).xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
    (hxh : ∀ i, coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ ((C i).xh:ℝ))
    (hh : 0 < coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet))
    (hnu : 0 < nu) (hl : 1 ≤ lambda)
    (hside : nu*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet) ≤ (S.card:ℝ))
    (hupper : (S.card:ℝ) ≤ ymax*Fintype.card V) (hhalf : 2*(S.card:ℝ) ≤ Fintype.card V)
    (hprofileSide : ∀ i, profileSixteenUpper i*ymax ≤ ((C i).side:ℝ))
    (hcheck : ∀ i, kappa ≤ profileQuadratic nu lambda (max 1 ((C i).alpha:ℝ))
      (profileIntervalMinimizer nu lambda (max 1 ((C i).alpha:ℝ)) (profileSixteenLower i) (profileSixteenUpper i))) :
    kappa*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*S.card ≤
      (Fintype.card (truncatedCut G S (roundedCutCap lambda S)).edgeSet:ℝ) := by
  have hspos : (0:ℝ) < S.card := (mul_pos hnu hh).trans_le hside
  have hS : S.Nonempty := card_pos.mp (by exact_mod_cast hspos)
  have hp := truncated_cut_positive_profile_table (kappa:=kappa) G S (roundedCutCap lambda S)
    (coverCutStrength (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet)))
    profileSixteenLower profileSixteenUpper (fun i => max 1 ((C i).alpha:ℝ))
    hh hn hS hl hnu ((le_div_iff₀ hh).mpr hside) (roundedCutCap_lower lambda S)
  apply (show kappa*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*S.card ≤
    ((truncatedCut G S (roundedCutCap lambda S)).edgeSet.ncard:ℝ) from ?_).trans_eq
      (by rw [Set.fintypeCard_eq_ncard])
  apply hp ?_ profile_sixteen_cover ?_ hcheck
  · intro X hXS
    apply cover_irreducible_exact_strength G hn hm hx hI X
    have hcard : (X.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card hXS
    linarith only [hcard,hhalf]
  · intro i t ht0 ht1 hlo hhi
    have hid : t*((S.card:ℝ)/coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet))/
        ((Fintype.card V:ℝ)/coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet))=
          t*(S.card:ℝ)/Fintype.card V := by field_simp
    rw [hid]
    apply rat_cut_profile_sound (C i) (hC i) (hxl i) (hxh i) (by positivity)
    have hscale : (S.card:ℝ)/Fintype.card V ≤ ymax := (div_le_iff₀ hn).mpr hupper
    have hhi0 : 0 ≤ profileSixteenUpper i := ht0.le.trans hhi
    have hmul := mul_le_mul hhi hscale (div_pos hspos hn).le hhi0
    have hmul' : t*(S.card:ℝ)/Fintype.card V ≤ profileSixteenUpper i*ymax := by
      simpa only [mul_div_assoc] using hmul
    exact hmul'.trans (hprofileSide i)

end
end Cycle12
