import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap006
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(119239/1000),119,(239/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,784360388534779316570671974773397018⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((119239/1000):ℚ):ℝ)≤(784360388534779316570671974773397018:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap006
