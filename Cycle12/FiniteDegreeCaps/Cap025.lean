import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap025
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(143591/1000),143,(591/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,16795699945688221187876399706957768773641286⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((143591/1000):ℚ):ℝ)≤(16795699945688221187876399706957768773641286:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap025
