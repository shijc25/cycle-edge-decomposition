import Cycle12.CountingSlope

namespace Cycle12
open Real
noncomputable section

theorem fixed_count_mgf_from_zero_lower {p residual theta slope : ℝ}
    (hp : 0 ≤ p) (hr : residual ≤ p) (ht : 0 < theta)
    (hs : exp theta-1 ≤ theta*slope) :
    1-residual+residual*exp theta ≤ exp (theta*slope*p) := by
  have ha : 0 ≤ exp theta-1 := sub_nonneg.mpr (one_le_exp_iff.mpr ht.le)
  have hx : residual*(exp theta-1) ≤ theta*slope*p := by
    calc
      _ ≤ p*(exp theta-1) := mul_le_mul_of_nonneg_right hr ha
      _ ≤ p*(theta*slope) := mul_le_mul_of_nonneg_left hs hp
      _ = _ := by ring
  have hh := Real.add_one_le_exp (residual*(exp theta-1))
  calc
    _ = residual*(exp theta-1)+1 := by ring
    _ ≤ exp (residual*(exp theta-1)) := hh
    _ ≤ _ := exp_le_exp.mpr hx

/-- The entire count-of-labels summand, including the rounded number of
marks, is dominated by a single negative exponential in the true scale. -/
theorem counting_union_exponent_bound {R z D p pl theta slope intercept M logUpper aa : ℝ}
    {t : ℕ} (hR : 0 < R) (hD : D*R ≤ z) (hp : pl ≤ p)
    (htheta : 0 ≤ theta) (hslope : 0 ≤ slope) (hitc : 0 ≤ intercept)
    (hmarks : (t:ℝ) ≤ M*R)
    (hlog : log (1+exp (theta*(1-slope*pl))) ≤ logUpper)
    (haa : aa ≤ theta*intercept*D-M*logUpper) :
    2*exp (-theta*(intercept*z))*(1+exp (theta-theta*slope*p))^t ≤ 2*exp (-aa*R) := by
  have harg : theta-theta*slope*p ≤ theta*(1-slope*pl) := by
    have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg htheta hslope)
    nlinarith only [hh]
  have hlog0 : 0 ≤ log (1+exp (theta-theta*slope*p)) :=
    log_nonneg (by linarith only [exp_pos (theta-theta*slope*p)])
  have hlogBound : log (1+exp (theta-theta*slope*p)) ≤ logUpper := by
    apply (log_le_log (by positivity : 0 < 1+exp (theta-theta*slope*p))
      (add_le_add le_rfl (exp_le_exp.mpr harg))).trans hlog
  have hlogUpper0 : 0 ≤ logUpper := hlog0.trans hlogBound
  have hfirst := mul_le_mul_of_nonneg_left hD (mul_nonneg htheta hitc)
  have hsecond := (mul_le_mul_of_nonneg_left hlogBound (Nat.cast_nonneg t)).trans
    (mul_le_mul_of_nonneg_right hmarks hlogUpper0)
  have hrate := mul_le_mul_of_nonneg_right haa hR.le
  have hexp : -theta*(intercept*z)+(t:ℝ)*log (1+exp (theta-theta*slope*p)) ≤ -aa*R := by
    nlinarith only [hfirst,hsecond,hrate]
  have hpow : (1+exp (theta-theta*slope*p))^t =
      exp ((t:ℝ)*log (1+exp (theta-theta*slope*p))) := by
    rw [exp_nat_mul,exp_log (by positivity)]
  rw [hpow,mul_assoc,← exp_add]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) (by norm_num)

end
end Cycle12
