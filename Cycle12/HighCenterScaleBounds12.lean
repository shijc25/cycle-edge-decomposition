import Cycle12.HighCenterCompletionGates12
import Cycle12.ScaleHalflines12

namespace Cycle12.Global12
open Real
noncomputable section

theorem high_center_power_envelope {w : ℝ} (hw : wA ≤ w) :
    (2:ℝ)^50*w ≤ (2:ℝ)^((2*s-rho)*w) := by
  have he : (2:ℝ)^(67:ℝ) ≤ (2:ℝ)^((2*s-rho)*wA) :=
    rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [s,rho,wA])
  have hb : (0:ℝ)+(2:ℝ)^50*wA ≤ (2:ℝ)^((2*s-rho)*wA) :=
    (show (0:ℝ)+(2:ℝ)^50*wA ≤ (2:ℝ)^(67:ℝ) by norm_num [wA]).trans he
  have hs : (2:ℝ)^50 ≤ log 2*(2*s-rho)*(0+(2:ℝ)^50*wA) := by
    have hl := log_two_lower
    norm_num [s,rho,wA]
    nlinarith only [hl]
  simpa only [zero_add] using linear_power_envelope (by norm_num [wA]) hb hs hw

/-- Actual current scale bounds, including a strengthened 2^45 minimum
for the smaller allowance determined by the untouched completion bank. -/
theorem high_center_scale_bounds {w r n : ℝ} (hw : wA ≤ w)
    (hrlo : (2:ℝ)^(s*w) ≤ r) (hrhi : r ≤ (2:ℝ)^(rho*w))
    (hn : n ≤ (1+1/2048)*r) (hn0 : 0<n) :
    let a := (2:ℝ)^(alpha*w)
    let h := completion_bank*(2:ℝ)^(s*w)
    1 ≤ a ∧ (2:ℝ)^24*a ≤ r ∧
      (2:ℝ)^45 ≤ min a (h^2/(2*r)) ∧
      (2:ℝ)^26*log n ≤ min a (h^2/(2*r)) := by
  dsimp only
  have hw1 : 1 ≤ w := (show (1:ℝ) ≤ wA by norm_num [wA]).trans hw
  have hr0 : 0<r := (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).trans_le hrlo
  have hp := high_center_power_envelope hw
  have hpa : (2:ℝ)^((2*s-rho)*w) ≤ (2:ℝ)^(alpha*w) :=
    rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by norm_num [s,rho,alpha]) (by linarith only [hw1]))
  have hamin : (2:ℝ)^45 ≤ (2:ℝ)^(alpha*w) := by
    have hb : (2:ℝ)^45 ≤ (2:ℝ)^50*w := by norm_num; linarith only [hw1]
    exact hb.trans (hp.trans hpa)
  have hsepPow : (2:ℝ)^(24:ℝ) ≤ (2:ℝ)^((s-alpha)*w) := by
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ s-alpha by norm_num [s,alpha])
    have hb : (24:ℝ) ≤ (s-alpha)*wA := by norm_num [s,alpha,wA]
    exact hb.trans hh
  have hsep : (2:ℝ)^24*(2:ℝ)^(alpha*w) ≤ r := by
    have hh := mul_le_mul_of_nonneg_right hsepPow (rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (alpha*w))
    rw [←rpow_add (by norm_num : (0:ℝ)<2) ((s-alpha)*w) (alpha*w),show (s-alpha)*w+alpha*w=s*w by ring] at hh
    have hh' := hh.trans hrlo
    norm_num at hh' ⊢
    exact hh'
  have hidentity : completion_bank^2*(2:ℝ)^((2*s-rho)*w)*(2:ℝ)^(rho*w)=
      (completion_bank*(2:ℝ)^(s*w))^2 := by
    rw [mul_assoc,←rpow_add (by norm_num : (0:ℝ)<2),show (2*s-rho)*w+rho*w=(s*w)*2 by ring]
    have hh := rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) (s*w) 2
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
    ring
  have haux {k : ℝ} (hk : 0 ≤ k) (hkb : 2*k ≤ completion_bank^2*(2:ℝ)^((2*s-rho)*w)) :
      k ≤ (completion_bank*(2:ℝ)^(s*w))^2/(2*r) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hm₁ := mul_le_mul_of_nonneg_left hrhi (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hk)
    have hm₂ := mul_le_mul_of_nonneg_right hkb (rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (rho*w))
    rw [hidentity] at hm₂
    nlinarith only [hm₁,hm₂]
  have ht67 : (2:ℝ)^(67:ℝ) ≤ (2:ℝ)^((2*s-rho)*w) := by
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*s-rho by norm_num [s,rho])
    exact (show (67:ℝ) ≤ (2*s-rho)*wA by norm_num [s,rho,wA]).trans hh
  have hauxmin : (2:ℝ)^45 ≤ (completion_bank*(2:ℝ)^(s*w))^2/(2*r) := by
    apply haux (by positivity)
    exact (show 2*(2:ℝ)^45 ≤ completion_bank^2*(2:ℝ)^(67:ℝ) by norm_num [completion_bank]).trans
      (mul_le_mul_of_nonneg_left ht67 (sq_nonneg _))
  have hauxlinear : (2:ℝ)^27*w ≤ (completion_bank*(2:ℝ)^(s*w))^2/(2*r) := by
    apply haux (by positivity)
    have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg completion_bank)
    have hc : (2:ℝ)^28 ≤ completion_bank^2*(2:ℝ)^50 := by norm_num [completion_bank]
    have hm := mul_le_mul_of_nonneg_right hc (by linarith only [hw1] : 0 ≤ w)
    nlinarith only [hh,hm]
  have hnup : n ≤ 2*(2:ℝ)^(rho*w) := by nlinarith only [hn,hrhi,hr0]
  have hlog := log_le_log hn0 hnup
  rw [log_mul (by norm_num : (2:ℝ)≠0) (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne',
    log_rpow (by norm_num : (0:ℝ)<2)] at hlog
  have hlogtwo : log 2 ≤ 1 := by have hh := Cycle13.log_two_24_digits.2; linarith only [hh]
  have hm := mul_le_mul_of_nonneg_left hlogtwo
    (show 0 ≤ 1+rho*w from add_nonneg (by norm_num)
      (mul_nonneg (by norm_num [rho]) (le_trans zero_le_one hw1)))
  have hrw : 1+rho*w ≤ 2*w := by
    have hh := mul_le_mul_of_nonneg_right (show rho ≤ (3/2:ℝ) by norm_num [rho])
      (by linarith only [hw1] : 0 ≤ w)
    have hw2 : 2 ≤ w := (show (2:ℝ) ≤ wA by norm_num [wA]).trans hw
    linarith only [hh,hw2]
  have hlogbound : log n ≤ 2*w := by nlinarith only [hlog,hm,hrw]
  have hlogscale := mul_le_mul_of_nonneg_left hlogbound (by norm_num : (0:ℝ) ≤ (2:ℝ)^26)
  refine ⟨(show (1:ℝ) ≤ (2:ℝ)^45 by norm_num).trans hamin,hsep,le_min hamin hauxmin,le_min ?_ ?_⟩
  · norm_num only [Nat.reducePow] at hp hlogscale
    nlinarith only [hp,hpa,hlogscale,hw1]
  · norm_num only [Nat.reducePow] at hauxlinear hlogscale
    linarith only [hauxlinear,hlogscale]

end
end Cycle12.Global12
