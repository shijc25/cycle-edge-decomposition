import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap010
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(126329/1000),126,(329/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,106860775661305767981799913138043897589⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((126329/1000):ℚ):ℝ)≤(106860775661305767981799913138043897589:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap010
