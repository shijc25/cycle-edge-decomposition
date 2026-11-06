import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap078
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(76111/500),152,(111/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,6658677787678561657711803870837937961122951918⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((76111/500):ℚ):ℝ)≤(6658677787678561657711803870837937961122951918:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap078
