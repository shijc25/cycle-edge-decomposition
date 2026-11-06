import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap039
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(157857/1000),157,(857/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,330896387250763815507700453637257128049470731007⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((157857/1000):ℚ):ℝ)≤(330896387250763815507700453637257128049470731007:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap039
