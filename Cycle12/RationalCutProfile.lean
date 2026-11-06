import Cycle12.CoverCutProfileBaseline
import Cycle12.RationalDegreeEnvelope
import Cycle12.CoverProfileCoordinates

namespace Cycle12
open Real Cycle13.MixedSample

structure RatCutProfile where
  side : ℚ
  xl : ℚ
  xh : ℚ
  leftLo : ℚ
  leftHi : ℚ
  rightLo : ℚ
  rightHi : ℚ
  cubeLo : ℚ
  cubeHi : ℚ
  ratio : ℚ
  alpha : ℚ

def RatCutProfile.shi (c : RatCutProfile) : ℚ := c.side*c.leftHi+(1-c.side)*c.rightHi
def RatCutProfile.cb (c : RatCutProfile) : ℚ := (1-c.cubeHi)/c.side
def RatCutProfile.ca (c : RatCutProfile) : ℚ := (1-c.shi)/c.side

def RatCutProfile.Valid (c : RatCutProfile) : Prop :=
  0 < c.side ∧ c.side ≤ 1/2 ∧ 0 ≤ c.xl ∧ c.xl ≤ c.xh ∧ c.xh ≤ 17/250 ∧
  0 ≤ c.leftLo ∧ 0 ≤ c.leftHi ∧ 0 ≤ c.rightLo ∧ 0 ≤ c.rightHi ∧ 0 ≤ c.cubeLo ∧ 0 ≤ c.cubeHi ∧
  c.leftLo^2 ≤ c.side ∧ c.side ≤ c.leftHi^2 ∧ c.rightLo^2 ≤ 1-c.side ∧ 1-c.side ≤ c.rightHi^2 ∧
  c.cubeLo^3 ≤ (c.side*c.leftLo+(1-c.side)*c.rightLo)^2 ∧ c.shi^2 ≤ c.cubeHi^3 ∧
  99/125 ≤ c.cubeLo ∧ c.cubeLo ≤ 1 ∧ c.cubeHi ≤ 1 ∧ c.shi ≤ 1 ∧ 0 ≤ c.ratio ∧
  c.ratio ≤ (c.cb+3*c.xl*c.ca)/ratCoverH c.xl ∧
  c.ratio ≤ (c.cb+3*c.xh*c.ca)/ratCoverH c.xh ∧
  c.alpha ≤ c.ratio*(ratCoverDen c.xl/(1-c.cubeLo*ratCoverW c.xl/3))

instance instDecidableRatCutProfileValid (c : RatCutProfile) : Decidable c.Valid := by
  unfold RatCutProfile.Valid
  infer_instance

noncomputable section

def RatCutProfile.realCertificate (c : RatCutProfile) (hc : c.Valid) : CoverCutProfileCertificate := by
  obtain ⟨hside,hhalf,hxl,horder,hmax,ha,hb,hd,he,hl,hu,ha2,hb2,hd2,he2,hl3,hu3,
    hlower,hl1,hu1,hshi,hr0,hrl,hrh,halpha⟩ := hc
  have hsideR : (0:ℝ) < (c.side:ℝ) := by exact_mod_cast hside
  have hhalfR : (c.side:ℝ) ≤ 1/2 := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hhalf
    norm_num at hh ⊢
    exact hh
  have hside1 : (c.side:ℝ) ≤ 1 := by linarith only [hhalfR]
  have hroots := cutShape_bounds_of_roots hsideR.le hside1
    (show (0:ℝ) ≤ (c.leftLo:ℝ) by exact_mod_cast ha)
    (show (0:ℝ) ≤ (c.leftHi:ℝ) by exact_mod_cast hb)
    (show (0:ℝ) ≤ (c.rightLo:ℝ) by exact_mod_cast hd)
    (show (0:ℝ) ≤ (c.rightHi:ℝ) by exact_mod_cast he)
    (show (0:ℝ) ≤ (c.cubeLo:ℝ) by exact_mod_cast hl)
    (show (0:ℝ) ≤ (c.cubeHi:ℝ) by exact_mod_cast hu)
    (by exact_mod_cast ha2) (by exact_mod_cast hb2) (by exact_mod_cast hd2) (by exact_mod_cast he2)
    (by exact_mod_cast hl3) (by
      have hh := (Rat.cast_le (K:=ℝ)).mpr hu3
      simpa only [RatCutProfile.shi,Rat.cast_pow,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_one] using hh)
  refine {
    side := (c.side:ℝ), xl := (c.xl:ℝ), xh := (c.xh:ℝ), alpha := (c.alpha:ℝ),
    cb := (c.cb:ℝ), ca := (c.ca:ℝ), u := (c.cubeLo:ℝ), ratio := (c.ratio:ℝ),
    side_pos := hsideR, side_half := hhalfR,
    xl_nonneg := by exact_mod_cast hxl,
    xmax := ?_, cb_nonneg := ?_, ca_nonneg := ?_, u_lower := ?_, u_upper := by exact_mod_cast hl1,
    shapeS := ?_, shapeU := ?_, shape_lower := hroots.2.2.1,
    ratio_nonneg := by exact_mod_cast hr0,
    ratio_left := ?_, ratio_right := ?_, alpha_bound := ?_ }
  · have hh := (Rat.cast_le (K:=ℝ)).mpr hmax
    norm_num at hh ⊢
    exact hh
  · have hh : 0 ≤ c.cb := div_nonneg (sub_nonneg.mpr hu1) hside.le
    exact_mod_cast hh
  · have hh : 0 ≤ c.ca := div_nonneg (sub_nonneg.mpr hshi) hside.le
    exact_mod_cast hh
  · have hh := (Rat.cast_le (K:=ℝ)).mpr hlower
    norm_num at hh ⊢
    exact hh
  · simp only [RatCutProfile.ca,Rat.cast_div,Rat.cast_sub,Rat.cast_one,div_mul_cancel₀ _ hsideR.ne']
    have hh := hroots.2.1
    simpa only [RatCutProfile.shi,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_one]
      using sub_le_sub_left hh 1
  · simp only [RatCutProfile.cb,Rat.cast_div,Rat.cast_sub,Rat.cast_one,div_mul_cancel₀ _ hsideR.ne']
    exact sub_le_sub_left hroots.2.2.2 1
  · simpa only [rat_cover_h_cast,Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]
      using (Rat.cast_le (K:=ℝ)).mpr hrl
  · simpa only [rat_cover_h_cast,Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]
      using (Rat.cast_le (K:=ℝ)).mpr hrh
  · simpa only [rat_cover_den_cast,rat_cover_w_cast,Rat.cast_div,Rat.cast_sub,Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat]
      using (Rat.cast_le (K:=ℝ)).mpr halpha

theorem rat_cut_profile_sound (c : RatCutProfile) (hc : c.Valid) {x y : ℝ}
    (hxl : (c.xl:ℝ) ≤ x) (hxh : x ≤ (c.xh:ℝ)) (hy : 0 < y) (hside : y ≤ (c.side:ℝ)) :
    max 1 (c.alpha:ℝ) ≤ coverCutStrength x y := by
  let C := c.realCertificate hc
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24⟩
  have hh := cover_cut_profile_certificate_bound C hxl hxh hy hside
  exact max_le (cover_cut_strength_ge_one (C.xl_nonneg.trans hxl) (hxh.trans C.xmax) hy
    (hside.trans C.side_half)) hh

end
end Cycle12
