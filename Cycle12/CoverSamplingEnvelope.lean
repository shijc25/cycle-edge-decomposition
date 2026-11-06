import Cycle12.CoverSampleCoordinates

namespace Cycle12
noncomputable section

theorem cover_order_lower {x xh s0 s n : ℝ}
    (hx : 0 < x) (hxxh : x ≤ xh) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) :
    4*(43/10)^3*s0^2/(coverScaleW xh)^3 ≤ n := by
  rw [hn]
  have hw := cover_w_pos hx
  have hwh := cover_w_mono hx.le hxxh
  gcongr

theorem cover_floor_correction {x s n : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) :
    1/(n*coverScaleW x)=(coverScaleW x)^2/(4*(43/10)^3*s^2) := by
  have hw := cover_w_pos hx
  rw [hn]
  field_simp

theorem cover_floor_parameter_envelope {xl x xh s0 s n : ℝ}
    (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hx : 0 < x) (hxxh : x ≤ xh)
    (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) :
    coverScaleP0 xl-(coverScaleW xh)^2/(4*(43/10)^3*s0^2) ≤
      (⌊coverSampleP x*n⌋₊:ℝ)/(n*coverScaleW x) ∧
    (⌊coverSampleP x*n⌋₊:ℝ)/(n*coverScaleW x) ≤ coverScaleP0 xh := by
  have hs := hs0.trans_le hss
  have hw := cover_w_pos hx
  have hn0 : 0 < n := by rw [hn]; positivity
  have hP : 0 ≤ coverScaleP0 x := (by norm_num : (0:ℝ) ≤ 99/200).trans (cover_p0_lower hx.le)
  have hh := cover_floor_ratio_bounds hn0 hw hP
  rw [← cover_p_w_identity x] at hh
  rw [cover_floor_correction hx hs hn] at hh
  have hc : (coverScaleW x)^2/(4*(43/10:ℝ)^3*s^2) ≤
      (coverScaleW xh)^2/(4*(43/10:ℝ)^3*s0^2) := by
    have hwh := cover_w_mono hx.le hxxh
    gcongr
  exact ⟨(sub_le_sub (cover_p0_mono hxl hxlx) hc).trans hh.1,
    hh.2.trans (cover_p0_mono hx.le hxxh)⟩

theorem cover_sample_order_lower {x xh s0 s n P lower : ℝ}
    (hx : 0 < x) (hxxh : x ≤ xh) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hlower : 0 ≤ lower) (hP : lower ≤ P)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) :
    4*(43/10)^3*lower*s0^2/(coverScaleW xh)^2 ≤ P*coverScaleW x*n := by
  have hw := cover_w_pos hx
  have hwh := cover_w_mono hx.le hxxh
  have hid : P*coverScaleW x*n=4*(43/10)^3*P*s^2/(coverScaleW x)^2 := by
    rw [hn]
    field_simp
    <;> ring
  rw [hid]
  have hP0 := hlower.trans hP
  gcongr

theorem cover_sample_probability_envelope {xl x xh P lower upper : ℝ}
    (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hxxh : x ≤ xh)
    (hlower : 0 ≤ lower) (hl : lower ≤ P) (hu : P ≤ upper) :
    lower*coverScaleW xl ≤ P*coverScaleW x ∧ P*coverScaleW x ≤ upper*coverScaleW xh := by
  have hx := hxl.trans hxlx
  constructor
  · exact mul_le_mul hl (cover_w_mono hxl hxlx) (cover_w_nonneg xl) (hlower.trans hl)
  · exact mul_le_mul hu (cover_w_mono hx hxxh) (cover_w_nonneg x) ((hlower.trans hl).trans hu)

end
end Cycle12
