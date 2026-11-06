import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap035
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(155359/1000),155,(359/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,58575917027307481933431853115410391538217977357⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((155359/1000):ℚ):ℝ)≤(58575917027307481933431853115410391538217977357:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap035
