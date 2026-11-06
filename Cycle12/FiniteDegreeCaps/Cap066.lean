import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap066
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(39589/250),158,(89/250),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,467633907102027744244712899001195203251276138272⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((39589/250):ℚ):ℝ)≤(467633907102027744244712899001195203251276138272:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap066
