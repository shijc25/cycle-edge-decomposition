import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap073
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(68687/500),137,(187/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,225784759863019948870530981952638304322580⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((68687/500):ℚ):ℝ)≤(225784759863019948870530981952638304322580:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap073
