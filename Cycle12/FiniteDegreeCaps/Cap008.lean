import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap008
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(12263/100),122,(63/100),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,8228266858852988835091968937069229441⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((12263/100):ℚ):ℝ)≤(8228266858852988835091968937069229441:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap008
