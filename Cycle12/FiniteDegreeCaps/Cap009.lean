import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap009
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(123863/1000),123,(863/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,19340974526261641571430635405901671174⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((123863/1000):ℚ):ℝ)≤(19340974526261641571430635405901671174:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap009
