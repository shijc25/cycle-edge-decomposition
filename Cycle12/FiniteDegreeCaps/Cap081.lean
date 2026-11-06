import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap081
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(79053/500),158,(53/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,393231676133183692412166711040079927132271328944⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((79053/500):ℚ):ℝ)≤(393231676133183692412166711040079927132271328944:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap081
