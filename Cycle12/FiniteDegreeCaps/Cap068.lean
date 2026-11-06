import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap068
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(63781/500),127,(281/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,251181880142616485903247814849825681574⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((63781/500):ℚ):ℝ)≤(251181880142616485903247814849825681574:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap068
