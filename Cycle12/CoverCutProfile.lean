import Cycle12.CoverSampleCoordinates
import Cycle12.Foundations.MixedCutShapeBounds

namespace Cycle12
open Real Cycle13.MixedSample
noncomputable section

def coverProfileValue (cb ca u x : ℝ) : ℝ :=
  (cb+3*x*ca)/coverScaleH x*(coverScaleDen x/(1-u*coverScaleW x/3))
def coverCutStrength (x y : ℝ) : ℝ :=
  coverProfileValue ((1-cutShapeU y)/y) ((1-cutShapeS y)/y) (cutShapeU y) x

theorem cover_profile_den_pos {u x : ℝ} (hu : u ≤ 1) (hx : 0 ≤ x) (hmax : x ≤ 17/250) :
    0 < 1-u*coverScaleW x/3 := by
  have hw := (cover_w_mono hx hmax).trans (show coverScaleW (17/250) ≤ 1/2 by norm_num [coverScaleW])
  have hh := mul_le_mul_of_nonneg_right hu (cover_w_nonneg x)
  linarith only [hw,hh]

theorem cover_profile_ratio_interval {cb ca lower xl x xh : ℝ}
    (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hxxh : x ≤ xh)
    (hl : lower ≤ (cb+3*xl*ca)/coverScaleH xl)
    (hu : lower ≤ (cb+3*xh*ca)/coverScaleH xh) :
    lower ≤ (cb+3*x*ca)/coverScaleH x := by
  have hx := hxl.trans hxlx
  have hxh := hx.trans hxxh
  apply (le_div_iff₀ (cover_h_pos hx)).mpr
  have hl' := (le_div_iff₀ (cover_h_pos hxl)).mp hl
  have hu' := (le_div_iff₀ (cover_h_pos hxh)).mp hu
  unfold coverScaleH at *
  by_cases hs : 0 ≤ 3*ca-lower*(351/200)
  · have hh := mul_nonneg hs (sub_nonneg.mpr hxlx)
    nlinarith only [hh,hl']
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hxxh)
    nlinarith only [hh,hu']

theorem cover_profile_factor_mono {u xl x : ℝ}
    (hu : 99/125 ≤ u) (hu1 : u ≤ 1) (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hmax : x ≤ 17/250) :
    coverScaleDen xl/(1-u*coverScaleW xl/3) ≤ coverScaleDen x/(1-u*coverScaleW x/3) := by
  apply (div_le_div_iff₀ (cover_profile_den_pos hu1 hxl (hxlx.trans hmax))
    (cover_profile_den_pos hu1 (hxl.trans hxlx) hmax)).mpr
  have hh := mul_nonneg (show 0 ≤ u/3-33/125 by linarith only [hu])
    (sub_nonneg.mpr (cover_w_mono hxl hxlx))
  unfold coverScaleDen
  nlinarith only [hh]

theorem cover_profile_interval_lower {cb ca u lower xl x xh : ℝ}
    (hlower : 0 ≤ lower) (hu : 99/125 ≤ u) (hu1 : u ≤ 1)
    (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hxxh : x ≤ xh) (hmax : xh ≤ 17/250)
    (hl : lower ≤ (cb+3*xl*ca)/coverScaleH xl)
    (hh : lower ≤ (cb+3*xh*ca)/coverScaleH xh) :
    lower*(coverScaleDen xl/(1-u*coverScaleW xl/3)) ≤ coverProfileValue cb ca u x := by
  have hr := cover_profile_ratio_interval hxl hxlx hxxh hl hh
  exact mul_le_mul hr (cover_profile_factor_mono hu hu1 hxl hxlx (hxxh.trans hmax))
    (div_nonneg (cover_den_pos hxl ((hxlx.trans hxxh).trans hmax)).le
      (cover_profile_den_pos hu1 hxl ((hxlx.trans hxxh).trans hmax)).le) (hlower.trans hr)

structure CoverCutProfileCertificate where
  side : ℝ
  xl : ℝ
  xh : ℝ
  alpha : ℝ
  cb : ℝ
  ca : ℝ
  u : ℝ
  ratio : ℝ
  side_pos : 0 < side
  side_half : side ≤ 1/2
  xl_nonneg : 0 ≤ xl
  xmax : xh ≤ 17/250
  cb_nonneg : 0 ≤ cb
  ca_nonneg : 0 ≤ ca
  u_lower : 99/125 ≤ u
  u_upper : u ≤ 1
  shapeS : ca*side ≤ 1-cutShapeS side
  shapeU : cb*side ≤ 1-cutShapeU side
  shape_lower : u ≤ cutShapeU side
  ratio_nonneg : 0 ≤ ratio
  ratio_left : ratio ≤ (cb+3*xl*ca)/coverScaleH xl
  ratio_right : ratio ≤ (cb+3*xh*ca)/coverScaleH xh
  alpha_bound : alpha ≤ ratio*(coverScaleDen xl/(1-u*coverScaleW xl/3))

/-- Both endpoint ratios suffice even when the ratio decreases in x.
The conclusion covers every smaller cut side, including all quantized bins. -/
theorem cover_cut_profile_certificate_bound (C : CoverCutProfileCertificate) {x y : ℝ}
    (hxl : C.xl ≤ x) (hxh : x ≤ C.xh) (hy : 0 < y) (hyC : y ≤ C.side) :
    C.alpha ≤ coverCutStrength x y := by
  have hx := C.xl_nonneg.trans hxl
  have hxmax := hxh.trans C.xmax
  have hy1 : y ≤ 1 := by linarith only [hyC,C.side_half]
  have hs1 : C.side ≤ 1 := by linarith only [C.side_half]
  have hcb : C.cb ≤ (1-cutShapeU y)/y :=
    ((le_div_iff₀ C.side_pos).mpr C.shapeU).trans (cutShapeU_secant hy hyC hs1)
  have hca : C.ca ≤ (1-cutShapeS y)/y :=
    ((le_div_iff₀ C.side_pos).mpr C.shapeS).trans (cutShapeS_secant hy hyC hs1)
  have hu : C.u ≤ cutShapeU y := C.shape_lower.trans (cutShapeU_antitone hy.le hyC C.side_half)
  have hU1 := cutShapeU_le_one hy.le hy1
  have hr : (C.cb+3*x*C.ca)/coverScaleH x ≤
      ((1-cutShapeU y)/y+3*x*((1-cutShapeS y)/y))/coverScaleH x := by
    apply div_le_div_of_nonneg_right _ (cover_h_pos hx).le
    exact add_le_add hcb (mul_le_mul_of_nonneg_left hca (by positivity))
  have hf : coverScaleDen x/(1-C.u*coverScaleW x/3) ≤
      coverScaleDen x/(1-cutShapeU y*coverScaleW x/3) := by
    apply div_le_div_of_nonneg_left (cover_den_pos hx hxmax).le (cover_profile_den_pos hU1 hx hxmax)
    have hh := mul_le_mul_of_nonneg_right hu (cover_w_nonneg x)
    linarith only [hh]
  have hnum : 0 ≤ ((1-cutShapeU y)/y+3*x*((1-cutShapeS y)/y))/coverScaleH x := by
    apply div_nonneg _ (cover_h_pos hx).le
    exact add_nonneg (C.cb_nonneg.trans hcb) (mul_nonneg (by positivity) (C.ca_nonneg.trans hca))
  exact (C.alpha_bound.trans (cover_profile_interval_lower C.ratio_nonneg C.u_lower C.u_upper
    C.xl_nonneg hxl hxh C.xmax C.ratio_left C.ratio_right)).trans
    (mul_le_mul hr hf (div_nonneg (cover_den_pos hx hxmax).le
      (cover_profile_den_pos C.u_upper hx hxmax).le) hnum)

end
end Cycle12
