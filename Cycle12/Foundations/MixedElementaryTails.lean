import Cycle12.Foundations.MixedDegreeTails

namespace Cycle13.MixedSample
open Real
noncomputable section

def orderFailure (x s c : ℝ) : ℝ :=
  exp (-poissonRate (s^2*sampleOrder x) (c*(s^2*sampleOrder x)))

theorem orderFailure_on_cell {x hi s₀ s c rate : ℝ}
    (hx : 0 < x) (hxh : x ≤ hi) (hhi : hi ≤ xmax)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hrate0 : 0 ≤ rate) (hrate : rate ≤ poissonRate 1 c) :
    orderFailure x s c ≤ exp (-rate*(s₀^2*sampleOrder hi)) := by
  have hsp := hs₀.trans_le hs
  have hμ : 0 < s^2*sampleOrder x := mul_pos (sq_pos_of_pos hsp) (sampleOrder_pos hx)
  have hμlo : 0 ≤ s₀^2*sampleOrder hi := mul_nonneg (sq_nonneg _) (sampleOrder_pos (hx.trans_le hxh)).le
  have hμmono : s₀^2*sampleOrder hi ≤ s^2*sampleOrder x :=
    mul_le_mul (pow_le_pow_left₀ hs₀.le hs 2) (sampleOrder_antitone hx hxh hhi)
      (sampleOrder_pos (hx.trans_le hxh)).le (sq_nonneg s)
  have he : poissonRate (s^2*sampleOrder x) (c*(s^2*sampleOrder x))=
      (s^2*sampleOrder x)*poissonRate 1 c := by
    have hh := poissonRate_scale (s:=s^2*sampleOrder x) (μ:=1) (a:=c) hμ.ne'
    simpa only [mul_one,mul_comm c] using hh
  unfold orderFailure
  rw [he]
  apply exp_le_exp.mpr
  nlinarith [mul_le_mul hμmono hrate hrate0 hμ.le]

def edgeCount (x s : ℝ) : ℝ := s^3*(order x)^2/2

def normalizedVariance (x s : ℝ) : ℝ :=
  (w x)^4/(8*216^2*(P x)^2*s^3)+(1-p x)*(w x)^2/(216*P x*s)

def varianceBox (lo hi s₀ : ℝ) : ℝ :=
  (w hi)^4/(8*216^2*(P lo)^2*s₀^3)+(1-p lo)*(w hi)^2/(216*P lo*s₀)

theorem edgeCount_pos {x s : ℝ} (hx : 0 < x) (hs : 0 < s) : 0 < edgeCount x s := by
  unfold edgeCount
  positivity [order_pos hx]

theorem normalizedVariance_nonneg {x s : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) (hs : 0 < s) :
    0 ≤ normalizedVariance x s := by
  have hp := p_lt_one hx.le hxmax
  have hP := P_pos hx.le
  unfold normalizedVariance
  positivity

theorem variance_normalization {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    sampleVarianceScalar (p x) (s^2*order x) (edgeCount x s)=
      (edgeCount x s*(p x)^2)^2*normalizedVariance x s := by
  have hw := (w_pos hx).ne'
  have hP := (P_pos hx.le).ne'
  have hs' := hs.ne'
  unfold sampleVarianceScalar normalizedVariance edgeCount order p
  field_simp
  <;> ring

theorem normalizedVariance_le_box {lo x hi s₀ s : ℝ}
    (hlo : 0 ≤ lo) (hx : 0 < x) (hlx : lo ≤ x) (hxh : x ≤ hi) (hhi : hi ≤ xmax)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) : normalizedVariance x s ≤ varianceBox lo hi s₀ := by
  have hsp := hs₀.trans_le hs
  have hP₀ := P_pos hlo
  have hP := P_pos hx.le
  have hPm := P_mono hlo hlx
  have hwm := w_mono hx.le hxh
  have hpm := p_mono hlo hlx
  have hpx := p_lt_one hx.le (hxh.trans hhi)
  have hp₀ : p lo < 1 := hpm.trans_lt hpx
  have hw4 := pow_le_pow_left₀ (w_nonneg x) hwm 4
  have hden₁ : 8*216^2*(P lo)^2*s₀^3 ≤ 8*216^2*(P x)^2*s^3 := by
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP₀.le hPm 2) (by norm_num))
      (pow_le_pow_left₀ hs₀.le hs 3) (pow_nonneg hs₀.le 3)
    positivity
  have hn₂ : (1-p x)*(w x)^2 ≤ (1-p lo)*(w hi)^2 :=
    mul_le_mul (by linarith) (pow_le_pow_left₀ (w_nonneg x) hwm 2)
      (sq_nonneg _) (by linarith)
  have hden₂ : 216*P lo*s₀ ≤ 216*P x*s :=
    mul_le_mul (mul_le_mul_of_nonneg_left hPm (by norm_num)) hs hs₀.le (by positivity)
  unfold normalizedVariance varianceBox
  apply add_le_add
  · exact (div_le_div_of_nonneg_right hw4 (by positivity)).trans
      (div_le_div_of_nonneg_left (pow_nonneg (w_nonneg hi) 4) (by positivity) hden₁)
  · exact (div_le_div_of_nonneg_right hn₂ (by positivity)).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity) hden₂)

theorem edgeFailure_eq_normalized {x s deviation : ℝ}
    (hx : 0 < x) (hxmax : x ≤ xmax) (hs : 0 < s) (hd : 0 < deviation) :
    sampleEdgeFailureScalar (p x) (s^2*order x) (edgeCount x s)
      (deviation*(edgeCount x s*(p x)^2))=
      normalizedVariance x s/(normalizedVariance x s+deviation^2) := by
  have hv := normalizedVariance_nonneg hx hxmax hs
  have hA : 0 < edgeCount x s*(p x)^2 := mul_pos (edgeCount_pos hx hs) (sq_pos_of_pos (p_pos hx))
  unfold sampleEdgeFailureScalar
  rw [variance_normalization hx hs]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  ring

theorem edgeFailure_on_cell {lo x hi s₀ s deviation : ℝ}
    (hlo : 0 ≤ lo) (hx : 0 < x) (hlx : lo ≤ x) (hxh : x ≤ hi) (hhi : hi ≤ xmax)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hd : 0 < deviation) :
    sampleEdgeFailureScalar (p x) (s^2*order x) (edgeCount x s)
      (deviation*(edgeCount x s*(p x)^2)) ≤
      varianceBox lo hi s₀/(varianceBox lo hi s₀+deviation^2) := by
  have hsp := hs₀.trans_le hs
  have hv := normalizedVariance_nonneg hx (hxh.trans hhi) hsp
  have hm := normalizedVariance_le_box hlo hx hlx hxh hhi hs₀ hs
  have hb := hv.trans hm
  rw [edgeFailure_eq_normalized hx (hxh.trans hhi) hsp hd]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg deviation)]

end
end Cycle13.MixedSample
