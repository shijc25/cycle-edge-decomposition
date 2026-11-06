import Cycle12.ProfileTruncation

namespace Cycle12
open Finset
noncomputable section

def profileQuadratic (nu lambda a t : ℝ) : ℝ := nu*(1-t)*(lambda-t)+a*t

def profileIntervalMinimizer (nu lambda a lo hi : ℝ) : ℝ :=
  min hi (max lo ((nu*(lambda+1)-a)/(2*nu)))

theorem profile_quadratic_difference (nu lambda a t u : ℝ) :
    profileQuadratic nu lambda a t-profileQuadratic nu lambda a u=
      (t-u)*(nu*(t+u)+a-nu*(lambda+1)) := by
  unfold profileQuadratic
  ring

/-- Exact minimization on a closed interval; endpoints remain part of
the feasible range. No floating-point critical-point choice is trusted. -/
theorem profile_interval_minimum {nu lambda a lo hi t : ℝ}
    (hnu : 0<nu) (hlo : lo ≤ t) (hhi : t ≤ hi) :
    profileQuadratic nu lambda a (profileIntervalMinimizer nu lambda a lo hi) ≤
      profileQuadratic nu lambda a t := by
  let b := (nu*(lambda+1)-a)/(2*nu)
  have hb : 2*nu*b=nu*(lambda+1)-a := by
    dsimp [b]
    field_simp
  have hlh := hlo.trans hhi
  by_cases hbl : b ≤ lo
  · have he : profileIntervalMinimizer nu lambda a lo hi=lo := by
      simp only [profileIntervalMinimizer,show (nu*(lambda+1)-a)/(2*nu)=b from rfl,
        max_eq_left hbl,min_eq_right hlh]
    rw [he]
    apply sub_nonneg.mp
    rw [profile_quadratic_difference]
    apply mul_nonneg (sub_nonneg.mpr hlo)
    have hh := mul_le_mul_of_nonneg_left hbl hnu.le
    have hh' := mul_le_mul_of_nonneg_left hlo hnu.le
    nlinarith only [hb,hh,hh']
  by_cases hhb : hi ≤ b
  · have he : profileIntervalMinimizer nu lambda a lo hi=hi := by
      simp only [profileIntervalMinimizer,show (nu*(lambda+1)-a)/(2*nu)=b from rfl,
        max_eq_right (le_of_not_ge hbl),min_eq_left hhb]
    rw [he]
    apply sub_nonneg.mp
    rw [profile_quadratic_difference]
    apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hhi)
    have hh := mul_le_mul_of_nonneg_left hhb hnu.le
    have hh' := mul_le_mul_of_nonneg_left hhi hnu.le
    nlinarith only [hb,hh,hh']
  · have he : profileIntervalMinimizer nu lambda a lo hi=b := by
      simp only [profileIntervalMinimizer,show (nu*(lambda+1)-a)/(2*nu)=b from rfl,
        max_eq_right (le_of_not_ge hbl),min_eq_right (le_of_not_ge hhb)]
    rw [he]
    apply sub_nonneg.mp
    rw [profile_quadratic_difference]
    have hid : (t-b)*(nu*(t+b)+a-nu*(lambda+1))=nu*(t-b)^2 := by
      have hab : a=nu*(lambda+1)-2*nu*b := by linarith only [hb]
      rw [hab]
      ring
    rw [hid]
    exact mul_nonneg hnu.le (sq_nonneg _)

theorem profile_quadratic_lower {nu nuLower lambda a A t : ℝ}
    (hn : nuLower ≤ nu) (hlambda : 1 ≤ lambda)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : a ≤ A) :
    profileQuadratic nuLower lambda a t ≤ nu*(1-t)*(lambda-t)+t*A := by
  have hc : 0 ≤ (1-t)*(lambda-t) := mul_nonneg (by linarith) (by linarith)
  have hh := mul_le_mul_of_nonneg_right hn hc
  have hh' := mul_le_mul_of_nonneg_left ha ht0
  unfold profileQuadratic
  nlinarith only [hh,hh']

/-- A finite interval certificate covers the whole light proportion
continuum. The profile hypotheses retain the argument t*nu/R. -/
theorem profile_finite_interval_bound {I : Type} [Fintype I]
    (lo hi lower : I → ℝ) (alpha : ℝ → ℝ) {nu nuLower R lambda kappa : ℝ}
    (hn : 0<nuLower) (hnu : nuLower ≤ nu) (hlambda : 1 ≤ lambda)
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ i, lo i ≤ t ∧ t ≤ hi i)
    (hprofile : ∀ i t, 0 ≤ t → t ≤ 1 → lo i ≤ t → t ≤ hi i → lower i ≤ alpha (t*nu/R))
    (hcheck : ∀ i, kappa ≤ profileQuadratic nuLower lambda (lower i)
      (profileIntervalMinimizer nuLower lambda (lower i) (lo i) (hi i)))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    kappa ≤ nu*(1-t)*(lambda-t)+t*alpha (t*nu/R) := by
  obtain ⟨i,hi0,hi1⟩ := hcover t ht0 ht1
  exact (hcheck i).trans ((profile_interval_minimum hn hi0 hi1).trans
    (profile_quadratic_lower hnu hlambda ht0 ht1 (hprofile i t ht0 ht1 hi0 hi1)))

end
end Cycle12
