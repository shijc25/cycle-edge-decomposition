import Cycle12.CoverScaleEnvelopes
import Cycle12.Foundations.ScaleTailBounds

namespace Cycle12
open Real Cycle13
noncomputable section

theorem cubic_two_parameter_exp_tail {u v a : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) (ha : 3 ≤ a) :
    u^2*v^3*exp (-a*(u*v)) ≤ exp (-a) := by
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hp : u^2 ≤ u^3 := pow_le_pow_right₀ hu (by decide : 2 ≤ 3)
  have hprod : u^2*v^3 ≤ (u*v)^3 := by
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hp (pow_nonneg hv0 3)
  have huv : 1 ≤ u*v := by nlinarith only [hu,hv,mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
  exact (mul_le_mul_of_nonneg_right hprod (exp_nonneg _)).trans
    (polynomial_exp_tail_scale (k:=3) huv ha)

theorem scaled_order_degree_tail {n nbase u v z zbase rate : ℝ}
    (hnbase : 0 ≤ nbase) (hu : 1 ≤ u) (hv : 1 ≤ v) (hrate : 0 ≤ rate)
    (hscale : 3 ≤ rate*zbase) (hn : n=nbase*u^2*v^3) (hz : zbase*(u*v) ≤ z) :
    n*exp (-rate*z) ≤ nbase*exp (-rate*zbase) := by
  have htail := cubic_two_parameter_exp_tail hu hv hscale
  have he : exp (-rate*z) ≤ exp (-(rate*zbase)*(u*v)) := by
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hz hrate
    nlinarith only [hh]
  rw [hn]
  calc
    _ ≤ nbase*u^2*v^3*exp (-(rate*zbase)*(u*v)) :=
      mul_le_mul_of_nonneg_left he (by positivity [show 0 ≤ v by linarith only [hv]])
    _ = nbase*(u^2*v^3*exp (-(rate*zbase)*(u*v))) := by ring
    _ ≤ nbase*exp (-(rate*zbase)) := mul_le_mul_of_nonneg_left htail hnbase
    _ = _ := by rw [neg_mul]

theorem cover_scaled_z_lower {xl x xh s0 s lower P zbase : ℝ}
    (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hx : 0 < x) (hxxh : x ≤ xh)
    (hmax : xh ≤ 17/250) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hlower : 0 ≤ lower) (hP : lower ≤ P)
    (hzbase : zbase ≤ 2*(43/10)^3*lower*coverScaleH xl*s0/(coverScaleW xh*coverScaleDen xl)) :
    zbase*((s/s0)*(coverScaleW xh/coverScaleW x)) ≤ coverScaleZ x s P := by
  have hw := cover_w_pos hx
  have hwh := cover_w_pos (hx.trans_le hxxh)
  have hd := cover_den_pos hx.le (hxxh.trans hmax)
  have hdl := cover_den_antitone hxl hxlx
  have hdxl := cover_den_pos hxl ((hxlx.trans hxxh).trans hmax)
  have hh0 := cover_h_pos hxl
  have hhx := cover_h_pos hx.le
  have hhm := cover_h_mono hxlx
  have hs := hs0.trans_le hss
  have hP0 := hlower.trans hP
  have hh := mul_le_mul_of_nonneg_right hzbase
    (show 0 ≤ (s/s0)*(coverScaleW xh/coverScaleW x) by positivity)
  have he : (2*(43/10:ℝ)^3*lower*coverScaleH xl*s0/(coverScaleW xh*coverScaleDen xl))*
      ((s/s0)*(coverScaleW xh/coverScaleW x))=
        2*(43/10)^3*lower*coverScaleH xl*s/(coverScaleW x*coverScaleDen xl) := by
    field_simp
  rw [he] at hh
  apply hh.trans
  unfold coverScaleZ
  gcongr

/-- The prefactor is the exact endpoint order. A rounded-down order must
not be substituted for it when certifying the degree union bound. -/
theorem cover_degree_uniform_scale {xl x xh s0 s lower P zbase rate n : ℝ}
    (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hx : 0 < x) (hxxh : x ≤ xh)
    (hmax : xh ≤ 17/250) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hlower : 0 ≤ lower) (hP : lower ≤ P)
    (hzbase : zbase ≤ 2*(43/10)^3*lower*coverScaleH xl*s0/(coverScaleW xh*coverScaleDen xl))
    (hrate : 0 ≤ rate) (hscale : 3 ≤ rate*zbase)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) :
    n*exp (-rate*coverScaleZ x s P) ≤
      (4*(43/10)^3*s0^2/(coverScaleW xh)^3)*exp (-rate*zbase) := by
  have hw := cover_w_pos hx
  have hwh := cover_w_pos (hx.trans_le hxxh)
  have hu : 1 ≤ s/s0 := (one_le_div hs0).mpr hss
  have hv : 1 ≤ coverScaleW xh/coverScaleW x := (one_le_div hw).mpr (cover_w_mono hx.le hxxh)
  apply scaled_order_degree_tail (u:=s/s0) (v:=coverScaleW xh/coverScaleW x)
    (by positivity) hu hv hrate hscale
  · rw [hn]
    field_simp
  · exact cover_scaled_z_lower hxl hxlx hx hxxh hmax hs0 hss hlower hP hzbase

end
end Cycle12
