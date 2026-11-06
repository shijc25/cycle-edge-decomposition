import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap024
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(143369/1000),143,(369/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,14400230651930939142935981534369464857602898⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((143369/1000):ℚ):ℝ)≤(14400230651930939142935981534369464857602898:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap024
