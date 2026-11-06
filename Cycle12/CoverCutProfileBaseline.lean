import Cycle12.CoverCutProfile

namespace Cycle12
open Real Cycle13.MixedSample
noncomputable section

def coverBasicCutProfile : CoverCutProfileCertificate where
  side := 1/2
  xl := 0
  xh := 17/250
  alpha := 1
  cb := 103/250
  ca := 117/200
  u := 99/125
  ratio := 1
  side_pos := by norm_num
  side_half := le_rfl
  xl_nonneg := le_rfl
  xmax := le_rfl
  cb_nonneg := by norm_num
  ca_nonneg := by norm_num
  u_lower := le_rfl
  u_upper := by norm_num
  shapeS := by
    have he : cutShapeS (1/2)=sqrt (1/2) := by norm_num [cutShapeS]; ring
    rw [he]
    have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)
    have hs0 := sqrt_nonneg (1/2:ℝ)
    nlinarith
  shapeU := by
    have hu0 := cutShapeU_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
    have hu : cutShapeU (1/2) ≤ 397/500 := by
      apply (pow_le_pow_iff_left₀ hu0 (by norm_num : (0:ℝ) ≤ 397/500) (by decide : (3:ℕ) ≠ 0)).mp
      rw [cutShapeU_half_cube]
      norm_num
    linarith only [hu]
  shape_lower := cutShapeU_denominator_lower (by norm_num) (by norm_num)
  ratio_nonneg := by norm_num
  ratio_left := by norm_num [coverScaleH]
  ratio_right := by norm_num [coverScaleH]
  alpha_bound := by norm_num [coverScaleDen,coverScaleW]

theorem cover_cut_strength_ge_one {x y : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ 17/250)
    (hy : 0 < y) (hyhalf : y ≤ 1/2) : 1 ≤ coverCutStrength x y :=
  cover_cut_profile_certificate_bound coverBasicCutProfile hx hxmax hy hyhalf

theorem cover_cut_strength_antitone_side {x y z : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ 17/250)
    (hy : 0 < y) (hyz : y ≤ z) (hzhalf : z ≤ 1/2) :
    coverCutStrength x z ≤ coverCutStrength x y := by
  have hz := hy.trans_le hyz
  have hz1 : z ≤ 1 := by linarith only [hzhalf]
  have hu1 := cutShapeU_le_one hz.le hz1
  have hs1 := cutShapeS_le_one hz.le hz1
  let C : CoverCutProfileCertificate := {
    side := z, xl := x, xh := x, alpha := coverCutStrength x z,
    cb := (1-cutShapeU z)/z, ca := (1-cutShapeS z)/z, u := cutShapeU z,
    ratio := ((1-cutShapeU z)/z+3*x*((1-cutShapeS z)/z))/coverScaleH x,
    side_pos := hz, side_half := hzhalf, xl_nonneg := hx, xmax := hxmax,
    cb_nonneg := div_nonneg (sub_nonneg.mpr hu1) hz.le,
    ca_nonneg := div_nonneg (sub_nonneg.mpr hs1) hz.le,
    u_lower := cutShapeU_denominator_lower hz.le hz1, u_upper := hu1,
    shapeS := by rw [div_mul_cancel₀ _ hz.ne'],
    shapeU := by rw [div_mul_cancel₀ _ hz.ne'],
    shape_lower := le_rfl,
    ratio_nonneg := by
      apply div_nonneg _ (cover_h_pos hx).le
      exact add_nonneg (div_nonneg (sub_nonneg.mpr hu1) hz.le)
        (mul_nonneg (by positivity) (div_nonneg (sub_nonneg.mpr hs1) hz.le)),
    ratio_left := le_rfl, ratio_right := le_rfl, alpha_bound := le_rfl }
  exact cover_cut_profile_certificate_bound C le_rfl le_rfl hy hyz

theorem cover_quantized_cut_profile_lower {x y grid alpha : ℝ}
    (hx : 0 ≤ x) (hxmax : x ≤ 17/250) (hy : 0 < y)
    (hgrid : y ≤ grid) (hgridhalf : grid ≤ 1/2) (ha : alpha ≤ coverCutStrength x grid) :
    max 1 alpha ≤ coverCutStrength x y :=
  max_le (cover_cut_strength_ge_one hx hxmax hy (hgrid.trans hgridhalf))
    (ha.trans (cover_cut_strength_antitone_side hx hxmax hy hgrid hgridhalf))

end
end Cycle12
