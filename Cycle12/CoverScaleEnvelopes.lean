import Cycle12.CoverSamplingEnvelope

namespace Cycle12
noncomputable section

def coverScaleR (x s : ℝ) : ℝ := 2*s*coverScaleDen x/(coverScaleH x*coverScaleW x)
def coverScaleZ (x s P : ℝ) : ℝ :=
  2*(43/10)^3*P*coverScaleH x*s/(coverScaleW x*coverScaleDen x)
def coverScaleD (x P : ℝ) : ℝ := (43/10)^3*P*(coverScaleH x)^2/(coverScaleDen x)^2
def coverScaleWgt (x s P : ℝ) : ℝ := 2*(43/10)^3*P^2*coverScaleH x*s/coverScaleDen x

theorem cover_scale_interval_lower {xl x xh s0 s lower P : ℝ}
    (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hx : 0 < x) (hxxh : x ≤ xh)
    (hmax : xh ≤ 17/250) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hlower : 0 ≤ lower) (hP : lower ≤ P) :
    2*s0*coverScaleDen xh/(coverScaleH xh*coverScaleW xh) ≤ coverScaleR x s ∧
    2*(43/10)^3*lower*coverScaleH xl*s0/(coverScaleW xh*coverScaleDen xl) ≤ coverScaleZ x s P ∧
    (43/10)^3*lower*(coverScaleH xl)^2/(coverScaleDen xl)^2 ≤ coverScaleD x P ∧
    2*(43/10)^3*lower^2*coverScaleH xl*s0/coverScaleDen xl ≤ coverScaleWgt x s P := by
  have hxmax := hxxh.trans hmax
  have hxhl := hx.le.trans hxxh
  have hw := cover_w_pos hx
  have hwh := cover_w_mono hx.le hxxh
  have hh0 := cover_h_pos hxl
  have hh := cover_h_pos hx.le
  have hhl := cover_h_mono hxlx
  have hhu := cover_h_mono hxxh
  have hd0 := cover_den_pos hxhl hmax
  have hd := cover_den_pos hx.le hxmax
  have hdl := cover_den_antitone hxl hxlx
  have hdu := cover_den_antitone hx.le hxxh
  have hs := hs0.trans_le hss
  have hP0 := hlower.trans hP
  have hwh0 := cover_w_nonneg xh
  have hhh0 := cover_h_pos hxhl
  refine ⟨?_,?_,?_,?_⟩
  · unfold coverScaleR
    gcongr
  · unfold coverScaleZ
    gcongr
  · unfold coverScaleD
    gcongr
  · unfold coverScaleWgt
    gcongr

theorem cover_scale_relations {x s P n : ℝ}
    (hx : 0 < x) (hxmax : x ≤ 17/250) (hs : 0 < s)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) :
    coverScaleZ x s P/coverScaleR x s=coverScaleD x P ∧
    coverScaleW x*P*coverScaleZ x s P=coverScaleWgt x s P ∧
    coverScaleR x s*coverScaleZ x s P=coverScaleW x*P*n := by
  have hw := cover_w_pos hx
  have hh := cover_h_pos hx.le
  have hd := cover_den_pos hx.le hxmax
  rw [hn]
  unfold coverScaleR coverScaleZ coverScaleD coverScaleWgt
  constructor
  · field_simp <;> ring
  constructor <;> field_simp <;> ring

end
end Cycle12
