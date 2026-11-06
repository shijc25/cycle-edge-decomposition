import Cycle12.ProfileIntervalMinimum

namespace Cycle12
open Finset SimpleGraph Cycle13
noncomputable section

def clampedHeavy (nu lambda alpha : ℝ) : ℝ :=
  min nu (max 0 ((alpha-(lambda-1)*nu)/2))

def clampedRetention (nu lambda alpha : ℝ) : ℝ :=
  alpha-((alpha-(lambda-1)*nu)*clampedHeavy nu lambda alpha-
    (clampedHeavy nu lambda alpha)^2)/nu

theorem clamped_concave_maximum {nu c y : ℝ} (hn : 0 ≤ nu)
    (hy0 : 0 ≤ y) (hyn : y ≤ nu) :
    c*y-y^2 ≤ c*min nu (max 0 (c/2))-(min nu (max 0 (c/2)))^2 := by
  by_cases hc0 : c/2 ≤ 0
  · rw [max_eq_left hc0,min_eq_right hn]
    have hc : c ≤ 0 := by linarith
    have hm := mul_nonpos_of_nonpos_of_nonneg hc hy0
    nlinarith [sq_nonneg y]
  · rw [max_eq_right (le_of_not_ge hc0)]
    by_cases hcn : nu ≤ c/2
    · rw [min_eq_left hcn]
      have hp : 0 ≤ (nu-y)*(c-nu-y) := mul_nonneg (sub_nonneg.mpr hyn) (by linarith)
      nlinarith only [hp]
    · rw [min_eq_right (le_of_not_ge hcn)]
      nlinarith [sq_nonneg (y-c/2)]

/-- The heavy population is constrained to [0,nu]. The exact clamped
bound, including both boundary cases, agrees with the scalar verifier. -/
theorem clamped_retention_profile_bound {nu lambda alpha t : ℝ}
    (hn : 0 < nu) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    clampedRetention nu lambda alpha ≤ profileQuadratic nu lambda alpha t := by
  have hy0 : 0 ≤ nu*(1-t) := mul_nonneg hn.le (sub_nonneg.mpr ht1)
  have hyn : nu*(1-t) ≤ nu := by nlinarith
  have hh := clamped_concave_maximum hn.le hy0 hyn (c:=alpha-(lambda-1)*nu)
  have hd := div_le_div_of_nonneg_right hh hn.le
  have he : profileQuadratic nu lambda alpha t=
      alpha-((alpha-(lambda-1)*nu)*(nu*(1-t))-(nu*(1-t))^2)/nu := by
    unfold profileQuadratic
    field_simp
    <;> ring
  rw [he]
  unfold clampedRetention clampedHeavy
  linarith only [hd]

attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem truncated_cut_clamped_retained (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    {h nu lambda alpha : ℝ} (hh : 0 < h) (hn : 0 < nu) (hl : 1 ≤ lambda)
    (hside : nu ≤ (S.card:ℝ)/h) (hcap : lambda*S.card ≤ (k:ℝ))
    (hprofile : ∀ X⊆S, alpha*h*X.card ≤ (cutSize G X:ℝ)) :
    clampedRetention nu lambda alpha*h*S.card ≤ ((truncatedCut G S k).edgeSet.ncard:ℝ) := by
  have hs : (0:ℝ) < S.card := by
    have hp : 0 < (S.card:ℝ)/h := hn.trans_le hside
    exact (div_pos_iff.mp hp).elim (fun h => h.1) (fun h => (not_lt_of_ge hh.le h.2).elim)
  have hS : S.Nonempty := card_pos.mp (by exact_mod_cast hs)
  obtain ⟨t,ht0,ht1,ht⟩ := truncated_cut_full_profile_scaled G S k (fun _ => alpha)
    (N:=1) hh (by norm_num) hS hcap (fun X hX => hprofile X hX)
  have hquad := profile_quadratic_lower hside hl ht0 ht1 (le_refl alpha)
  have hb := (clamped_retention_profile_bound hn ht0 ht1).trans (hquad.trans ht)
  have hc := (le_div_iff₀ (mul_pos hh hs)).mp hb
  nlinarith only [hc]

end
end Cycle12
