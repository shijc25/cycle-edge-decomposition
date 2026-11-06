import Cycle12.Foundations.MixedSampleCoordinates
import Cycle12.Foundations.SampleTailScale

namespace Cycle13
open Real
noncomputable section

theorem poissonRate_mono_mean {a μ₀ μ : ℝ} (ha : 0 < a) (hμ₀ : 0 < μ₀)
    (haμ : a ≤ μ₀) (hμ : μ₀ ≤ μ) : poissonRate μ₀ a ≤ poissonRate μ a := by
  have hμp := hμ₀.trans_le hμ
  have hlog0 : 0 ≤ log μ-log μ₀ := sub_nonneg.mpr (log_le_log hμ₀ hμ)
  have hlog := log_le_sub_one_of_pos (div_pos hμp hμ₀)
  rw [log_div hμp.ne' hμ₀.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hμ₀.le
  have he : μ₀*(μ/μ₀-1)=μ-μ₀ := by field_simp <;> ring
  rw [he] at hm
  have ha' := mul_le_mul_of_nonneg_right haμ hlog0
  unfold poissonRate
  rw [log_div ha.ne' hμp.ne',log_div ha.ne' hμ₀.ne']
  nlinarith

theorem quadratic_exp_tail_above {s₀ s a N : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hN : 0 ≤ N) (ha : 2 ≤ a*s₀) :
    (s^2*N)*exp (-a*s) ≤ (s₀^2*N)*exp (-a*s₀) := by
  have ht : 1 ≤ s/s₀ := (one_le_div hs₀).mpr hs
  have hh := polynomial_exp_tail_scale (k:=2) ht ha
  calc
    _ = (s₀^2*N)*((s/s₀)^2*exp (-(a*s₀)*(s/s₀))) := by
      rw [show -(a*s₀)*(s/s₀)= -a*s by field_simp]
      field_simp <;> ring
    _ ≤ (s₀^2*N)*exp (-(a*s₀)) :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg _) hN)
    _ = _ := by ring_nf

namespace MixedSample

theorem order_pos {x : ℝ} (hx : 0 < x) : 0 < order x := by
  unfold order
  positivity [w_pos hx]

theorem order_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : order y ≤ order x := by
  unfold order
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos (w_pos hx) 3)
    (pow_le_pow_left₀ (w_pos hx).le (w_mono hx.le hxy) 3)

def degreeFailure (x s dm : ℝ) : ℝ :=
  (s^2*order x)*exp (-poissonRate ((s*z x)*mu x) ((s*z x)*dm))

theorem degreeFailure_on_positive_cell {lo x hi s₀ s dm rate : ℝ}
    (hlo : 0 < lo) (hlx : lo ≤ x) (hxh : x ≤ hi) (hhi : hi ≤ xmax)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hdm : 0 < dm) (hdmμ : dm ≤ mu lo)
    (hrate0 : 0 ≤ rate) (hrate : rate ≤ poissonRate (mu lo) dm)
    (htail : 2 ≤ rate*(s₀*z hi)) :
    degreeFailure x s dm ≤ (s₀^2*order lo)*exp (-rate*(s₀*z hi)) := by
  have hx := hlo.trans_le hlx
  have hz : 0 < z x := z_pos hx (hxh.trans hhi)
  have hzhi := z_pos (hx.trans_le hxh) hhi
  have hsp := hs₀.trans_le hs
  have hμ := poissonRate_mono_mean hdm (mu_pos hlo.le) hdmμ (mu_mono hlo.le hlx)
  have hr : rate ≤ poissonRate (mu x) dm := hrate.trans hμ
  have hzr : rate*z hi ≤ z x*poissonRate (mu x) dm := by
    have hh := mul_le_mul (z_antitone hx hxh hhi) hr hrate0 hz.le
    nlinarith
  have he : exp (-((s*z x)*poissonRate (mu x) dm)) ≤ exp (-(rate*z hi)*s) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hzr hsp.le]
  unfold degreeFailure
  rw [poissonRate_scale (mul_pos hsp hz).ne']
  calc
    _ ≤ (s^2*order lo)*exp (-(rate*z hi)*s) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (order_antitone hlo hlx) (sq_nonneg s)) he
        (exp_nonneg _) (mul_nonneg (sq_nonneg s) (order_pos hlo).le)
    _ ≤ (s₀^2*order lo)*exp (-(rate*z hi)*s₀) :=
      quadratic_exp_tail_above hs₀ hs (order_pos hlo).le (by nlinarith [htail])
    _ = _ := by ring_nf

/-- The first regime includes arbitrarily small positive `x`. Its divergent
order factor is paid for by the exponential degree tail, uniformly in scale. -/
theorem degreeFailure_near_zero {x y s₀ s dm rate : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ xmax)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hdm : 0 < dm) (hdmμ : dm ≤ mu 0)
    (hrate0 : 0 ≤ rate) (hrate : rate ≤ poissonRate (mu 0) dm)
    (htail : 6 ≤ rate*(s₀*z y)) :
    degreeFailure x s dm ≤ (s₀^2*order y)*exp (-rate*(s₀*z y)) := by
  have hyp := hx.trans_le hxy
  have hzy := z_pos hyp hy
  have hzx := z_pos hx (hxy.trans hy)
  have hsp := hs₀.trans_le hs
  have hμ := poissonRate_mono_mean hdm (mu_pos (by norm_num : (0:ℝ) ≤ 0)) hdmμ
    (mu_mono (by norm_num : (0:ℝ) ≤ 0) hx.le)
  have hr : rate ≤ poissonRate (mu x) dm := hrate.trans hμ
  have he : exp (-((s*z x)*poissonRate (mu x) dm)) ≤ exp (-(s*rate)*z x) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hr (mul_pos hsp hzx).le]
  have hscale : 6 ≤ (s*rate)*z y := by
    nlinarith [mul_le_mul_of_nonneg_right hs (mul_nonneg hrate0 hzy.le)]
  have hzbound := degree_tail_at_zero hx hxy hy hscale
  unfold degreeFailure
  rw [poissonRate_scale (mul_pos hsp hzx).ne']
  calc
    _ ≤ (s^2*order x)*exp (-(s*rate)*z x) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg s) (order_pos hx).le)
    _ = s^2*(order x*exp (-(s*rate)*z x)) := by ring
    _ ≤ s^2*(order y*exp (-(s*rate)*z y)) := mul_le_mul_of_nonneg_left hzbound (sq_nonneg s)
    _ = (s^2*order y)*exp (-(rate*z y)*s) := by ring_nf
    _ ≤ (s₀^2*order y)*exp (-(rate*z y)*s₀) :=
      quadratic_exp_tail_above hs₀ hs (order_pos hyp).le (by nlinarith [htail])
    _ = _ := by ring_nf

end MixedSample
end
end Cycle13
