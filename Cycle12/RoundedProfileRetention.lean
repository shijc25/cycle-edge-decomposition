import Cycle12.RoundedResidualJanson
import Cycle12.ProfileRectangle
import Cycle12.ClampedTruncation

namespace Cycle12
open Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]

/-- Exact rounded deletion loss, separated from the choice of a lower
bound for the pre-deletion truncated graph. -/
theorem rounded_residual_from_retained (G : SimpleGraph V) (S T : Finset V)
    {h nu lambda cap k0 kappa : ℝ} (hh : 0 < h) (hn : 0 < nu) (hl : 1 ≤ lambda)
    (hside : nu*h ≤ (S.card:ℝ)) (hmark : (T.card:ℝ) ≤ cap)
    (hbefore : k0*h*S.card ≤
      (Fintype.card (truncatedCut G S (roundedCutCap lambda S)).edgeSet:ℝ))
    (hkappa : kappa ≤ k0-(cap/h)*(lambda+1/(nu*h))) :
    kappa*h*S.card ≤
      (Fintype.card (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ) := by
  have hs : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  have hc : 0 ≤ cap := (Nat.cast_nonneg T.card).trans hmark
  have hcap := roundedCutCap_scaled_upper (show 0 ≤ lambda by linarith) (mul_pos hn hh) S hside
  have hmark' := mul_le_mul_of_nonneg_left hmark (Nat.cast_nonneg (α:=ℝ) (roundedCutCap lambda S))
  have hloss := mul_le_mul_of_nonneg_right hcap hc
  have hscale := mul_le_mul_of_nonneg_right hkappa hh.le
  have he : (cap/h)*(lambda+1/(nu*h))*h=cap*(lambda+1/(nu*h)) := by field_simp
  have hpay : cap*(lambda+1/(nu*h)) ≤ (k0-kappa)*h := by
    rw [sub_mul,he] at hscale
    nlinarith only [hscale]
  have hpay' := mul_le_mul_of_nonneg_right hpay hs
  have hd := truncated_residual_retention G S T (roundedCutCap lambda S) (rounded_cut_cap_ge_card S hl)
  nlinarith only [hbefore,hmark',hloss,hpay',hd]

theorem rounded_residual_clamped_retained (G : SimpleGraph V) (S T : Finset V)
    {h nu lambda alpha cap kappa : ℝ} (hh : 0 < h) (hn : 0 < nu) (hl : 1 ≤ lambda)
    (hside : nu*h ≤ (S.card:ℝ)) (hmark : (T.card:ℝ) ≤ cap)
    (hprofile : ∀ X⊆S, alpha*h*X.card ≤ (cutSize G X:ℝ))
    (hkappa : kappa ≤ clampedRetention nu lambda alpha-(cap/h)*(lambda+1/(nu*h))) :
    kappa*h*S.card ≤
      (Fintype.card (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ) := by
  apply rounded_residual_from_retained G S T hh hn hl hside hmark _ hkappa
  have hh' := truncated_cut_clamped_retained G S (roundedCutCap lambda S) hh hn hl
    ((le_div_iff₀ hh).mpr hside) (roundedCutCap_lower lambda S) hprofile
  simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using hh'

theorem rounded_residual_profile_table (G : SimpleGraph V) (S T : Finset V)
    (alpha : ℝ → ℝ) (lo hi lower : I → ℝ) {h N nu lambda cap k0 kappa : ℝ}
    (hh : 0 < h) (hN : 0 < N) (hn : 0 < nu) (hl : 1 ≤ lambda)
    (hside : nu*h ≤ (S.card:ℝ)) (hmark : (T.card:ℝ) ≤ cap)
    (hprofile : ∀ X⊆S, alpha ((X.card:ℝ)/N)*h*X.card ≤ (cutSize G X:ℝ))
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ i, lo i ≤ t ∧ t ≤ hi i)
    (hlower : ∀ i t, 0 ≤ t → t ≤ 1 → lo i ≤ t → t ≤ hi i →
      lower i ≤ alpha (t*(S.card/h)/(N/h)))
    (hcheck : ∀ i, k0 ≤ profileQuadratic nu lambda (lower i)
      (profileIntervalMinimizer nu lambda (lower i) (lo i) (hi i)))
    (hkappa : kappa ≤ k0-(cap/h)*(lambda+1/(nu*h))) :
    kappa*h*S.card ≤
      (Fintype.card (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ) := by
  have hS : S.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hn hh).trans_le hside)
  apply rounded_residual_from_retained G S T hh hn hl hside hmark _ hkappa
  have hp := truncated_cut_profile_table G S (roundedCutCap lambda S) alpha lo hi lower hh hN hS hl hn
    ((le_div_iff₀ hh).mpr hside) (roundedCutCap_lower lambda S) hprofile hcover hlower hcheck
  simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using hp

theorem rounded_residual_best_retained (G : SimpleGraph V) (S T : Finset V)
    {h nu lambda cap a b kappa : ℝ} (hh : 0 < h) (hn : 0 < nu) (hl : 1 ≤ lambda)
    (hside : nu*h ≤ (S.card:ℝ)) (hmark : (T.card:ℝ) ≤ cap)
    (ha : a*h*S.card ≤ (Fintype.card (truncatedCut G S (roundedCutCap lambda S)).edgeSet:ℝ))
    (hb : b*h*S.card ≤ (Fintype.card (truncatedCut G S (roundedCutCap lambda S)).edgeSet:ℝ))
    (hkappa : kappa ≤ max a b-(cap/h)*(lambda+1/(nu*h))) :
    kappa*h*S.card ≤
      (Fintype.card (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ) := by
  apply rounded_residual_from_retained G S T hh hn hl hside hmark _ hkappa
  rw [max_mul_of_nonneg _ _ hh.le,max_mul_of_nonneg _ _ (Nat.cast_nonneg (α:=ℝ) S.card)]
  exact max_le ha hb

end
end Cycle12
