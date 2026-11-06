import Cycle12.PowerScaleBounds

namespace Cycle12
open Real
noncomputable section

/-- A single value and slope check certify a linear function below a
base-two exponential on the complete right half-line. -/
theorem linear_power_envelope {a b t w0 w : ℝ}
    (hbase0 : 0≤a+b*w0) (hbase : a+b*w0≤(2:ℝ)^(t*w0))
    (hslope : b≤log 2*t*(a+b*w0)) (hw : w0≤w) :
    a+b*w≤(2:ℝ)^(t*w) := by
  have he := Real.add_one_le_exp (log 2*t*(w-w0))
  have hm := mul_le_mul_of_nonneg_left he hbase0
  have hs := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hw)
  have hlin : a+b*w≤(a+b*w0)*exp (log 2*t*(w-w0)) := by
    nlinarith only [hm,hs]
  apply hlin.trans
  have hh := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (log 2*t*(w-w0))).le
  convert hh using 1
  simp only [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  rw [← Real.exp_add]
  congr 1
  ring

theorem entropy_rate_halfline {rho s theta w0 w : ℝ}
    (hbase0 : 0≤(1001/1000:ℝ)+(rho-s)*w0)
    (hbase : (1001/1000:ℝ)+(rho-s)*w0≤(2:ℝ)^((theta-s)*w0))
    (hslope : rho-s≤log 2*(theta-s)*((1001/1000:ℝ)+(rho-s)*w0))
    (hw : w0≤w) :
    (2:ℝ)^(s*w)*((1001/1000:ℝ)+(rho-s)*w)≤(2:ℝ)^(theta*w) := by
  have hh := linear_power_envelope hbase0 hbase hslope hw
  have hm := mul_le_mul_of_nonneg_left hh
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s*w))
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)] at hm
  convert hm using 1
  congr 1
  ring

end
end Cycle12
