import Cycle12.CoverSampleCoordinates
import Cycle12.FixedMeanGaps

namespace Cycle12
noncomputable section

theorem cover_internal_gap_box (n k : ℕ) {nlo klo m alpha : ℝ}
    (hnlo : 1 < nlo) (hnn : nlo ≤ n) (hklo : 0 < klo) (hkk : klo ≤ k)
    (hm : 0 ≤ m) :
    ((1-alpha)-1/(klo*(1-1/nlo)))*(((k:ℝ)/n)^2*m) ≤
      m*fixedChooseRatio n k 2-alpha*((k:ℝ)/n)^2*m := by
  have hn1R : (1:ℝ) < n := hnlo.trans_le hnn
  have hn1 : 1 < n := by exact_mod_cast hn1R
  have hk0R : (0:ℝ) < k := hklo.trans_le hkk
  have hk0 : 0 < k := by exact_mod_cast hk0R
  have hnl0 : 0 < nlo := by linarith only [hnlo]
  have hfrac : 1/(n:ℝ) ≤ 1/nlo := one_div_le_one_div_of_le hnl0 hnn
  have hsub0 : 0 < 1-1/nlo := sub_pos.mpr ((div_lt_one hnl0).mpr hnlo)
  have hden : klo*(1-1/nlo) ≤ (k:ℝ)*(1-1/(n:ℝ)) :=
    mul_le_mul hkk (by linarith only [hfrac]) hsub0.le hk0R.le
  have hcorr := one_div_le_one_div_of_le (mul_pos hklo hsub0) hden
  have hh := mul_le_mul_of_nonneg_right
    (sub_le_sub_left hcorr (1-alpha)) (mul_nonneg (sq_nonneg ((k:ℝ)/n)) hm)
  exact hh.trans (fixed_internal_mean_gap n k hn1 hk0 hm)

theorem cover_incident_gap_scaled (x : ℝ) :
    coverSampleV x-2*coverSampleP x+(coverSampleP x)^2=
      coverScaleW x*(1+3*x)*coverIncidentGap (coverSampleV x) := by
  have hid := cover_incident_gap_identity (coverSampleV x)
  have hp : coverSampleP x=coverSampleV x*coverScaleA (coverSampleV x) := rfl
  rw [hp,← cover_v_w_identity,← hid]
  unfold coverScaleA
  ring

theorem cover_incident_gap_box (n k : ℕ) {xl x nlo Pu : ℝ}
    (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hx : 0 < x) (hxmax : x ≤ 17/250)
    (hnlo : 1 < nlo) (hnn : nlo ≤ n) (hk : k ≤ n)
    (hp : (k:ℝ)/n ≤ coverSampleP x) (hPu : coverScaleP0 x ≤ Pu) :
    ((1+3*xl)*coverIncidentGap (coverSampleV xl)-Pu/(nlo-1))*coverScaleW x ≤
      coverSampleV x-(1-fixedChooseRatio n (n-k) 2) := by
  have hn1R : (1:ℝ) < n := hnlo.trans_le hnn
  have hn1 : 1 < n := by exact_mod_cast hn1R
  have hgap := fixed_incident_mean_gap n k hn1 hk (v:=coverSampleV x) hp
    ((cover_sample_p_lt_half x hx.le hxmax).2.le.trans (by norm_num))
  have hg0 : 0 ≤ coverIncidentGap (coverSampleV xl) :=
    (by norm_num : (0:ℝ) ≤ 1/100).trans (cover_incident_gap_positive (cover_v_nonneg hxl))
  have hprod : (1+3*xl)*coverIncidentGap (coverSampleV xl) ≤
      (1+3*x)*coverIncidentGap (coverSampleV x) :=
    mul_le_mul (by linarith only [hxlx])
      (cover_incident_gap_mono (cover_v_nonneg hxl) (cover_v_mono hxl hxlx))
      hg0 (by linarith only [hx])
  have hP0 : 0 ≤ coverScaleP0 x :=
    (by norm_num : (0:ℝ) ≤ 99/200).trans (cover_p0_lower hx.le)
  have hcorr : coverScaleP0 x/((n:ℝ)-1) ≤ Pu/(nlo-1) := by
    apply (div_le_div_of_nonneg_right hPu (by linarith only [hn1R])).trans
    apply div_le_div_of_nonneg_left (hP0.trans hPu) (by linarith only [hnlo])
    linarith only [hnn]
  have hh := mul_le_mul_of_nonneg_right (sub_le_sub hprod hcorr) (cover_w_nonneg x)
  have he : ((1+3*x)*coverIncidentGap (coverSampleV x)-coverScaleP0 x/((n:ℝ)-1))*coverScaleW x=
      coverSampleV x-2*coverSampleP x+(coverSampleP x)^2-coverSampleP x/((n:ℝ)-1) := by
    rw [cover_incident_gap_scaled,cover_p_w_identity]
    ring
  rw [he] at hh
  exact hh.trans hgap

end
end Cycle12
