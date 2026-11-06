import Cycle12.CoverIncidentGap

namespace Cycle12
noncomputable section

def coverScaleW (x : ℝ) : ℝ := (43/10)^3*x^2
def coverScaleH (x : ℝ) : ℝ := 103/250+351/200*x
def coverScaleA (v : ℝ) : ℝ := 99/200+11/100*v+7/100*v^2
def coverScaleP0 (x : ℝ) : ℝ := (1+3*x)*coverScaleA (coverSampleV x)
def coverScaleDen (x : ℝ) : ℝ := 1-33/125*coverScaleW x
def coverScaleMu (x : ℝ) : ℝ := (1+447/100*x)/coverScaleH x

theorem cover_v_w_identity (x : ℝ) : coverSampleV x=coverScaleW x*(1+3*x) := rfl
theorem cover_p_w_identity (x : ℝ) : coverSampleP x=coverScaleW x*coverScaleP0 x := by
  simp only [coverSampleP,coverSampleV,coverScaleW,coverScaleP0,coverScaleA]
  ring

theorem cover_w_nonneg (x : ℝ) : 0 ≤ coverScaleW x := by unfold coverScaleW; positivity
theorem cover_w_pos {x : ℝ} (hx : 0 < x) : 0 < coverScaleW x := by unfold coverScaleW; positivity
theorem cover_w_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    coverScaleW x ≤ coverScaleW y := by unfold coverScaleW; gcongr

theorem cover_v_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ coverSampleV x := by
  rw [cover_v_w_identity]; positivity [cover_w_nonneg x]

theorem cover_v_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    coverSampleV x ≤ coverSampleV y := by
  rw [cover_v_w_identity,cover_v_w_identity]
  exact mul_le_mul (cover_w_mono hx hxy) (by linarith) (by linarith) (cover_w_nonneg y)

theorem cover_a_lower {v : ℝ} (hv : 0 ≤ v) : (99/200:ℝ) ≤ coverScaleA v := by
  unfold coverScaleA; nlinarith [sq_nonneg v]

theorem cover_a_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    coverScaleA u ≤ coverScaleA v := by unfold coverScaleA; gcongr

theorem cover_p0_lower {x : ℝ} (hx : 0 ≤ x) : (99/200:ℝ) ≤ coverScaleP0 x := by
  have ha := cover_a_lower (cover_v_nonneg hx)
  have hh := mul_nonneg hx (show 0 ≤ coverScaleA (coverSampleV x) by linarith)
  unfold coverScaleP0
  nlinarith only [ha,hh]

theorem cover_p0_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    coverScaleP0 x ≤ coverScaleP0 y := by
  have ha := cover_a_lower (cover_v_nonneg hx)
  exact mul_le_mul (by linarith) (cover_a_mono (cover_v_nonneg hx) (cover_v_mono hx hxy))
    (by linarith) (by linarith)

theorem cover_h_pos {x : ℝ} (hx : 0 ≤ x) : 0 < coverScaleH x := by unfold coverScaleH; positivity
theorem cover_h_mono {x y : ℝ} (hxy : x ≤ y) : coverScaleH x ≤ coverScaleH y := by
  unfold coverScaleH; linarith

theorem cover_den_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    coverScaleDen y ≤ coverScaleDen x := by
  have hh := cover_w_mono hx hxy
  unfold coverScaleDen; linarith

theorem cover_den_pos {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ 17/250) : 0 < coverScaleDen x := by
  have hh := cover_w_mono hx hxmax
  have hu : coverScaleW x ≤ 1/2 := hh.trans (by norm_num [coverScaleW])
  unfold coverScaleDen
  linarith only [hu]

theorem cover_mu_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    coverScaleMu x ≤ coverScaleMu y := by
  apply (div_le_div_iff₀ (cover_h_pos hx) (cover_h_pos (hx.trans hxy))).mpr
  unfold coverScaleH
  nlinarith only [hxy]

theorem cover_floor_ratio_bounds {n w P0 : ℝ} (hn : 0 < n) (hw : 0 < w)
    (hP : 0 ≤ P0) :
    P0-1/(n*w) ≤ (⌊w*P0*n⌋₊:ℝ)/(n*w) ∧ (⌊w*P0*n⌋₊:ℝ)/(n*w) ≤ P0 := by
  have hden := mul_pos hn hw
  constructor
  · apply (le_div_iff₀ hden).mpr
    have hh := (Nat.sub_one_lt_floor (w*P0*n)).le
    have hid : (P0-1/(n*w))*(n*w)=w*P0*n-1 := by field_simp <;> ring
    rw [hid]
    exact hh
  · apply (div_le_iff₀ hden).mpr
    have hh := Nat.floor_le (mul_nonneg (mul_nonneg hw.le hP) hn.le)
    nlinarith only [hh]

end
end Cycle12
