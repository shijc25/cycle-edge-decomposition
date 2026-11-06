import Cycle12.ReservoirSamplerParameters12

namespace Cycle12
open Cycle13 Real Finset
noncomputable section

theorem reservoir_sample_log_bounds :
    log (16/15:ℝ) ≤ 323/5000 ∧ (47/400:ℝ) ≤ log (9/8:ℝ) := by
  have h1 := (ratLog_argument_bounds (q := 16/15) (by norm_num) 3).2
  have h2 := (ratLog_argument_bounds (q := 9/8) (by norm_num) 3).1
  have hr1 : ratLogUpper (((16/15:ℚ)-1)/((16/15)+1)) 3 ≤ 323/5000 := by
    norm_num [ratLogUpper,ratLogPartial,sum_range_succ]
  have hr2 : (47/400:ℚ) ≤ ratLogPartial (((9/8:ℚ)-1)/((9/8)+1)) 3 := by
    norm_num [ratLogPartial,sum_range_succ]
  have hc1 := (Rat.cast_le (K := ℝ)).mpr hr1
  have hc2 := (Rat.cast_le (K := ℝ)).mpr hr2
  push_cast at hc1 hc2 h1 h2
  exact ⟨h1.trans hc1,hc2.trans h2⟩

theorem reservoir_poisson_rates {z R : ℝ} (hz : 0 < z) (hR : 0 < R) :
    z/256 ≤ poissonRate (3*z) ((45/16)*z) ∧
    R*z/192 ≤ poissonRate (R*z) ((9/8)*R*z) := by
  obtain ⟨hl1,hl2⟩ := reservoir_sample_log_bounds
  have hrate1 : poissonRate (3:ℝ) (45/16) = 3-45/16-(45/16)*log (16/15:ℝ) := by
    unfold poissonRate
    rw [show (45/16:ℝ)/3 = (16/15:ℝ)⁻¹ by norm_num,log_inv]
    ring
  have hrate2 : poissonRate (1:ℝ) (9/8) = 1-9/8+(9/8)*log (9/8:ℝ) := by
    simp [poissonRate]
  constructor
  · have hs := poissonRate_scale hz.ne' (μ := 3) (a := 45/16)
    rw [hrate1] at hs
    have he : poissonRate (3*z) ((45/16)*z) = z*(3-45/16-(45/16)*log (16/15:ℝ)) := by
      simpa only [mul_comm z] using hs
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hl1 hz.le
    nlinarith only [hh,hz]
  · have hs := poissonRate_scale (mul_pos hR hz).ne' (μ := 1) (a := 9/8)
    rw [hrate2] at hs
    have he : poissonRate (R*z) ((9/8)*R*z) = (R*z)*(1-9/8+(9/8)*log (9/8:ℝ)) := by
      convert hs using 1 <;> ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hl2 (mul_pos hR hz).le
    nlinarith only [hh,mul_pos hR hz]

theorem reservoir_sample_tail_bounds {n z R : ℝ} (hn : 0 < n)
    (hR : 12 ≤ R) (hzR : 1048576*R ≤ z) (hlog : 1024*log n ≤ z) :
    n*exp (-poissonRate (3*z) ((45/16)*z)) ≤ 1/1024 ∧
    exp (-poissonRate (R*z) ((9/8)*R*z)) ≤ 1/1024 := by
  have hR0 : 0 < R := by linarith only [hR]
  have hz : 512 ≤ z := by linarith only [hR,hzR]
  have hz0 : 0 < z := by linarith only [hz]
  obtain ⟨hd,hu⟩ := reservoir_poisson_rates hz0 hR0
  constructor
  · have hbig : 20 ≤ z/256-log n := by linarith only [hR,hzR,hlog]
    calc
      _ = exp (-(poissonRate (3*z) ((45/16)*z)-log n)) := by
        rw [neg_sub,exp_sub,exp_log hn,exp_neg]
        ring
      _ ≤ exp (-(z/256-log n)) := exp_le_exp.mpr (by linarith only [hd])
      _ ≤ _ := exp_neg_le_one_1024 hbig
  · have hbig : 20 ≤ R*z/192 := by
      have hh := mul_le_mul hR (show 512 ≤ z from hz) (by norm_num : (0:ℝ) ≤ 512) hR0.le
      nlinarith only [hh]
    exact (exp_le_exp.mpr (neg_le_neg hu)).trans (exp_neg_le_one_1024 hbig)

end
end Cycle12
