import Cycle12.FiniteLaplace

namespace Cycle12
open Real
noncomputable section

theorem beta_reflection_derivative_nonneg (a b p q x : ℝ)
    (ha : 0≤a) (hp : 0<p) (hpq : p≤q) (hx0 : 0≤x) (hxp : x<p)
    (hab : b*p≤a*q) :
    0≤a*(1/(p+x)+1/(p-x))-b*(1/(q-x)+1/(q+x)) := by
  have hq : 0<q := hp.trans_le hpq
  have hpx : 0<p-x := by linarith
  have hqx : 0<q-x := by linarith
  have hpx' : 0<p+x := by linarith
  have hqx' : 0<q+x := by linarith
  have hp2 : 0<p^2-x^2 := by nlinarith
  have hq2 : 0<q^2-x^2 := by nlinarith
  have hqp : 0≤q^2-p^2 := by nlinarith
  have hN : 0≤a*p*(q^2-x^2)-b*q*(p^2-x^2) := by
    have h₁ := mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) hq.le) hp2.le
    have h₂ := mul_nonneg (mul_nonneg ha hqp) (sq_nonneg x)
    nlinarith
  have he : a*(1/(p+x)+1/(p-x))-b*(1/(q-x)+1/(q+x))=
      2*(a*p*(q^2-x^2)-b*q*(p^2-x^2))/((p^2-x^2)*(q^2-x^2)) := by
    field_simp
    ring
  rw [he]
  exact div_nonneg (mul_nonneg (by norm_num) hN) (mul_pos hp2 hq2).le

end
end Cycle12
