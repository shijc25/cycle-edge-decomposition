import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap054
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(29887/250),119,(137/250),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,971703845929592150492965803656520377⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((29887/250):ℚ):ℝ)≤(971703845929592150492965803656520377:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap054
